
#include <pass.h>
#include <cgc_magics.h>
#include "llvm/Transforms/Utils/CallPromotionUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include <llvm/Transforms/Utils/BasicBlockUtils.h>
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/IR/CFG.h"
#include <algorithm>
#include <queue>

using namespace llvm;

#define DEBUG_TYPE "cgc"
#define cgcPassLog(M) LLVM_DEBUG(dbgs() << "CallgraphClonePass: " << M << "\n")
#define oprint(s) LLVM_DEBUG(dbgs() << s << "\n")

static cl::list<std::string>
HardenFunctions("cgc-harden-funcs",
    cl::desc("Specify all the comma-separated function regexes to harden against optimizer [default: main, LLVMFuzzerTestOneInput]"),
    cl::ZeroOrMore, cl::CommaSeparated, cl::NotHidden);

static cl::opt<std::string>
ClonePrefix("cgc-clone-prefix",
    cl::desc("Specify the clone name prefix"),
    cl::init("__cgc_"), cl::NotHidden);

static cl::opt<bool>
CGCFill("cgc-fill", 
cl::init(true), cl::NotHidden,
cl::desc("If true will clone all the other calls once the planned ones have been completed"));

// Fill 256Kb by default, an average size of L2 cache
static cl::opt<unsigned>
MaxSize("cgc-max-aflmap", 
cl::init(256*1024), cl::NotHidden,
cl::desc("The maximum acceptable size for the AFL++ edge map"));

namespace {
  // This pass clones function calls based on decisions taken by CGC Planner on which
  // subgraph portion of the callgraph should be cloned
  class CallgraphClonePass : public ModulePass {

    // Keep track of all the functions belonging to strongly connected components
    std::set<Function*> SCCFunctions;

    std::map<Function*, std::set<Function*>> FunctionToSCC;
    std::map<Function*, std::set<CallBase*>> FunctionToCallBases;
    std::map<Function*, unsigned long>       FunctionToAFLMapSize;

    // Keep track of cloned functions
    std::set<Function*> FunctionClones;

    // Return the priority of the CallBase, an higher priority means the CallBase
    // should be cloned earlier
    static long getPriority(CallBase *CB) {
        MDNode* N;
        assert(CB);
        N = CB->getMetadata(CGC_CLONE_PRIORITY);
        if (N == NULL) return 0;
        Constant *val = dyn_cast<ConstantAsMetadata>(N->getOperand(0))->getValue();
        assert(val);
        long prio = cast<ConstantInt>(val)->getSExtValue();
        return prio;
    }

    // Save the priority value for a function that has been cloned
    static void setFunctionPriority(Function *F, long prio) {
        LLVMContext& C = F->getContext();
        MDNode* N = MDNode::get(C, ConstantAsMetadata::get(ConstantInt::get(C, APInt(sizeof(unsigned long)*8, prio, true))));
        F->setMetadata(CGC_CLONE_PRIORITY, N);
    }

    // Return the priority of the Function that has been cloned with
    static long getFunctionPriority(Function *F) {
        MDNode* N;
        assert(F);
        N = F->getMetadata(CGC_CLONE_PRIORITY);
        if (N == NULL) return 0;
        Constant *val = dyn_cast<ConstantAsMetadata>(N->getOperand(0))->getValue();
        if(!val) return 0;
        long prio = cast<ConstantInt>(val)->getSExtValue();
        return prio;
    }

    // Compare the priority of two CallBases, an higher priority means the CallBase
    // should be cloned earlier
    struct ComparePriority {
        bool operator()(CallBase *c1, CallBase *c2) {
            long prio1 = getPriority(c1);
            long prio2 = getPriority(c2);
            return prio1 < prio2;
        }
    };

    // A priority queue for the CallBases, ordered by priority
    using CallBaseQueue = std::priority_queue<CallBase*, std::vector<CallBase*>, ComparePriority>;

  public:
    static char ID;
    unsigned long unique_id = 0;
    unsigned long nclones = 0;
    unsigned long aflmap_size = 0;
    CallgraphClonePass() : ModulePass(ID) {}

    unsigned long getUniqueID() {
        return ++unique_id;
    }

    // Taken from: https://github.com/AFLplusplus
    // True if block has successors and it dominates all of them.
    bool isFullDominator(const BasicBlock *BB, const DominatorTree *DT) {
        if (succ_begin(BB) == succ_end(BB)) return false;
        for (const BasicBlock *SUCC : make_range(succ_begin(BB), succ_end(BB))) {
            // if the edge is critical it will be splitted
            if (isCriticalEdge(BB->getTerminator(), SUCC)) continue;
            if (!DT->dominates(BB, SUCC)) return false;
        }
        return true;
    }

    // Taken from: https://github.com/AFLplusplus
    // True if block has predecessors and it postdominates all of them.
    bool isFullPostDominator(const BasicBlock *       BB,
                                    const PostDominatorTree *PDT) {
        if (pred_begin(BB) == pred_end(BB)) return false;
        for (const BasicBlock *PRED : make_range(pred_begin(BB), pred_end(BB))) {
            // if the edge is critical it will be splitted
            if (isCriticalEdge(PRED->getTerminator(), BB)) continue;
            if (!PDT->dominates(BB, PRED)) return false;
        }
        return true;
    }

    // Given a function, try to estimate the number of edges in the function that
    // will be instrumented by AFLplusplus.
    // It instruments edges by breaking all critial edges with a block in the middle
    // and avoiding instrumenting blocks which are full dominators, or full 
    // post-dominators with multiple predecessors.
    unsigned long estimateAFLEdges(Function *F) {
        DominatorTree *DT = &getAnalysis<DominatorTreeWrapperPass>(*F).getDomTree();
        PostDominatorTree *PDT = &getAnalysis<PostDominatorTreeWrapperPass>(*F).getPostDomTree();
        unsigned edges = 0;
        for (BasicBlock &BB: *F) {
            // Do not instrument full dominators, or full post-dominators with multiple
            // predecessors.
            bool shouldInstrumentBlock = (&F->getEntryBlock() == &BB) || (!isFullDominator(&BB, DT) && 
                                            !(isFullPostDominator(&BB, PDT) 
                                            && !BB.getSinglePredecessor()));
            if (shouldInstrumentBlock) ++edges;

            Instruction *TI = BB.getTerminator();
            if (TI->getNumSuccessors() > 1 && !isa<IndirectBrInst>(TI))
                for (unsigned succ = 0, end = TI->getNumSuccessors(); succ != end; ++succ) {
                    if (isCriticalEdge(TI, succ))
                        ++edges;
                }
        }
        return edges;
    }

    // Return true if `F` has been marked as a root from which to start cloning 
    // by CGC Planner.
    bool isCGCRoot(Function &F) {
        MDNode* N;
        N = F.getMetadata(CGC_ROOT_ATTR);
        if (N == NULL) return false;
        return true;
    }

    // Return true if `CB` has been planned to be cloned by CGC Planner
    bool isPlannedClone(CallBase &CB) {
        MDNode* N;
        N = CB.getMetadata(CGC_CLONE_CALL_ATTR);
        if (N == NULL) return false;
        return true;
    }

    // Return true if `F` has an available_externally linkage (i.e. equivalent to a declaration)
    bool isAvailableExternally(Function &F) {
        GlobalValue::LinkageTypes L = F.getLinkage();
        return GlobalValue::isAvailableExternallyLinkage(L);
    }

    // Substitute all the trailings .x.y.z that llvm creates when having two functions
    // with the same name, with some uniqueIDs to avoid long names
    std::string compressName(std::string name) {
        // find the last .num
        std::string newName = name;
        std::string::size_type idx = newName.rfind('.');
        if (idx == std::string::npos || idx == newName.length()) {
            return newName;
        }
        // ensure it is actually a number
        int random = atoi(newName.substr(idx+1).c_str());

        while (random) {
            newName = newName.substr(0, idx);
            idx = newName.rfind('.');
            if (idx == std::string::npos || idx == newName.length()) {
                return newName + "." + std::to_string(getUniqueID());
            }
            random = atoi(newName.substr(idx+1).c_str());
        }
        return newName + "." + std::to_string(getUniqueID());
    }

    void setCloneName(Function *F) {
        // if the function name already contains the prefix do not add it
        if (F->getName().find(ClonePrefix) == std::string::npos)
            F->setName(ClonePrefix + F->getName());
        // Compress the clone name to avoid .1452.3394.9208.13831.27566...
        // at the end
        F->setName(compressName(F->getName().str()));
    }

    // Replace all the dots in the name that llvm may insert with underscores
    void normalizeName(Function *F) {
        std::string newName = F->getName().str();
        std::replace(newName.begin(), newName.end(), '.', '_');
        F->setName(newName);
    }

    // Mark the function so that it can be recognized as a clone
    void markClone(Function *F) {
        LLVMContext& C = F->getContext();
        MDNode* N = MDNode::get(C, ConstantAsMetadata::get(ConstantInt::get(C, APInt(sizeof(unsigned long)*8, 1, true))));
        F->setMetadata(CGC_CLONE_MARK, N);

        // NOTICE: A bit risky to change all names
        std::string FName = F->getName().str();
        F->setName(CGC_CLONE_MARK + std::to_string(getFunctionPriority(F)) + "_" + FName);
    }

    // Visit a Constant AST to find and replace oldV with newV, returning a new constant
    Constant *replaceConstant(Constant *C, Constant *newV, Constant *oldV) {
        if (ConstantStruct *S = dyn_cast<ConstantStruct>(C)) {
            SmallVector<Constant*, 8> Ops;
            for (unsigned i = 0, e = S->getNumOperands(); i != e; ++i) {
                Constant *op = S->getOperand(i);
                if (op == oldV)
                    Ops.push_back(newV);
                else
                    Ops.push_back(replaceConstant(op, newV, oldV));
            }

            Constant* res = ConstantStruct::getAnon(Ops, true);
            return res;
        
        } else if (ConstantExpr *E = dyn_cast<ConstantExpr>(C)) {
            SmallVector<Constant*, 8> Ops;
            for (unsigned i = 0, e = E->getNumOperands(); i != e; ++i) {
                Constant *op = E->getOperand(i);
                if (op == oldV)
                    Ops.push_back(newV);
                else
                    Ops.push_back(replaceConstant(op, newV, oldV));
            }

            Constant *res = E->getWithOperands(Ops);
            return res;
            
        } else {
            return C;
        }
    }

    // Fix the prologue of newF, by substituting the occurencies of oldF.
    // This allows us to clone functions without corrupting the prologue, that is
    // left untouched by cloneFunction. -fsanitize=function uses prologues
    void fixPrologue(Function *newF, Function *oldF) {
        if (!newF->hasPrologueData()) return;

        Constant *prologue = replaceConstant(newF->getPrologueData(), newF, oldF);
        newF->setPrologueData(prologue);
    }

    // `dest` is a clone of `source`, with the instructions mapped 1to1 in the `VMap`.
    // Update the `FunctionToCallBases` struct to keep track of the CallBases in
    // `dest` that represent the clone CallBases of `source`.
    // Update the `FunctionToAFLMapSize` to keep track of the estimation for the
    // new clone.
    void updateMetadata(Function *dest, Function *source, ValueToValueMapTy &VMap) {
        assert(FunctionToCallBases.find(source) != FunctionToCallBases.end());
        FunctionToCallBases[dest];
        for (CallBase *CB: FunctionToCallBases[source]) {
            CallBase *mappedCB = dyn_cast<CallBase>(VMap[CB]);
            assert(mappedCB);
            FunctionToCallBases[dest].insert(mappedCB);
        }

        assert(FunctionToAFLMapSize.find(source) != FunctionToAFLMapSize.end());
        FunctionToAFLMapSize[dest] = FunctionToAFLMapSize[source];
    }

    // Gather all the calls to `F`, starting from `I` and visiting recursively all
    // the users of `I`, to collect all the eventual calls to `F` originated by `I`
    // e.g. call bitcast F, with I being the bitcast
    void gatherEventualCallsTo(Function *F, Value *V, std::set<Instruction*> &callsToF) {
        // If it is a call, just check if `F` is called
        if (CallBase * CB = dyn_cast<CallBase>(V)) {
            // check that the function is called and not passed as param
            if (CB->getCalledOperand()->stripPointerCasts() == F) {
                callsToF.insert(CB);
            }
        // If it is a bitcast, visit all the users recursively
        } else if (BitCastOperator * BO = dyn_cast<BitCastOperator>(V)) {
            for (User* user: BO->users()) {
                gatherEventualCallsTo(F, user, callsToF);
            }
        }
    }

    // Return true if `F` has multiple call sites so it makes sense to clone it
    bool shouldCloneFunction(Function *F) {
        // Do not clone LLVMFuzzerTestOneInput itself
        if (F->getName().equals("LLVMFuzzerTestOneInput")) return false;

        unsigned int numCallsToF = 0;
        std::set<Instruction*> callsToF;
        // Gather all the calls to the function `F`
        for (User* user: F->users()) {
            gatherEventualCallsTo(F, user, callsToF);

            // No need to visit all the users, bailout if already true
            if (callsToF.size() > 1) return true;
        }

        numCallsToF = callsToF.size();

        // oprint(F->getName().str() << " - " << numCallsToF);
        // We should clone the function only if it is called more than once
        return numCallsToF > 1;
    }

    // Return true if cloning `F` would not exceed the size limit.
    bool allowedToClone(Function *F) {
        unsigned long additional_edges = 0;
        // If `F` is in a SCC we will clone the whole SCC while cloning `F`
        if (isInSCC(F)) {
            assert(FunctionToSCC.find(F) != FunctionToSCC.end());
            std::set<Function*> SCC = FunctionToSCC[F];
            for (Function *F: SCC) {
                assert(FunctionToAFLMapSize.find(F) != FunctionToAFLMapSize.end());
                additional_edges += FunctionToAFLMapSize[F];
            }
        // Otherwise just count `F`
        } else {
            assert(FunctionToAFLMapSize.find(F) != FunctionToAFLMapSize.end());
            additional_edges += FunctionToAFLMapSize[F];
        }
        // More readable mf
        if (aflmap_size + additional_edges > MaxSize) return false;
        else return true;
    }

    // Return true if the `SCC` has multiple call sites so it makes sense to clone it
    bool shouldCloneSCC(std::set<Function*> &SCC) {
        unsigned int numCallsToSCC = 0;
        std::set<Instruction*> callsToSCC;
        // Gather all the calls to each function in the `SCC`
        for (Function *F: SCC) {
            for (User* user: F->users()) {
                gatherEventualCallsTo(F, user, callsToSCC);
            }
        }

        // Count only the calls from outside the `SCC`
        for (Instruction *call: callsToSCC) {
            Function* callerF = call->getParent()->getParent();
            if (SCC.find(callerF) == SCC.end())
                ++numCallsToSCC;
        }

        // for (Function *F: SCC)
        //     oprint(F->getName().str() << " - " << numCallsToSCC);
        // We should clone the function only if it is called more than once
        return numCallsToSCC > 1;
    }

    // Add all the callbases in the function to the priority queue
    void updateCallBaseQueue(CallBaseQueue &cgcCallBaseQueue, Function *F) {
        for (CallBase *CB: FunctionToCallBases[F]) {
            cgcCallBaseQueue.push(CB);
        }
    }

    // Update the metadata on SCC clones
    void updateSCCMetadata(Function *SCCclone, std::set<Function*> &SCCClones) {
        assert(FunctionToSCC.find(SCCclone) == FunctionToSCC.end());
        FunctionToSCC[SCCclone] = SCCClones;
        assert(SCCFunctions.find(SCCclone) == SCCFunctions.end());
        SCCFunctions.insert(SCCclone);
    }

    // Visit the Strongly Connected Component where `F` belongs, to clone it as 
    // a single node. Update `cgcCallBaseQueue` accordingly to continue the visit.
    Function* addSCCClone(CallBaseQueue &cgcCallBaseQueue, Function* F, long prio) {
        std::map<Function*, Function*> FtoClones;
        std::set<Function*> SCCClones;

        assert(FunctionToSCC.find(F) != FunctionToSCC.end());
        std::set<Function*> SCC = FunctionToSCC[F];

        // Clone all the functions in the SCC
        bool should_clone = shouldCloneSCC(SCC);
        for (Function *SCCfunc: SCC) {
            // Clone original function if required
            if (should_clone) {
                ValueToValueMapTy VMap;
                Function *clone = CloneFunction(SCCfunc, VMap);
                assert(clone);
                updateMetadata(clone, SCCfunc, VMap);
                trackClone(clone, cgcCallBaseQueue);
                setCloneName(clone);
                fixPrologue(clone, SCCfunc);
                FtoClones[SCCfunc] = clone;
                SCCClones.insert(clone);
                // Add the priority to the clone to keep track of it
                setFunctionPriority(clone, prio);
            } else {
                // Set the original function as a clone without updating the number of clones
                trackClone(SCCfunc, cgcCallBaseQueue, /*update=*/false);
                FtoClones[SCCfunc] = SCCfunc;
                SCCClones.insert(SCCfunc);
                // Add the priority to the clone to keep track of it
                setFunctionPriority(SCCfunc, prio);
            }
        }

        // update metadata for SCC
        for (Function *SCCclone: SCCClones) {
            if (FunctionToSCC.find(SCCclone) == FunctionToSCC.end())
                updateSCCMetadata(SCCclone, SCCClones);
        }

        // Now rewire the functions in the SCC clones
        for (Function *SCCclone: SCCClones) {
            assert(FunctionToCallBases.find(SCCclone) != FunctionToCallBases.end());
            for (CallBase *CB: FunctionToCallBases[SCCclone]) {

                // For direct calls, simply redirect target to new clone
                Function *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                if (C) {
                    Function *clone;
                    // If the called function is in the SCC use the clone we generated
                    if (FtoClones.find(C) != FtoClones.end()) {
                        clone = FtoClones[C];
                        if (clone->getFunctionType() != CB->getCalledOperand()->getType()->getPointerElementType())
                            CB->setCalledFunction(CB->getFunctionType(), CastInst::CreatePointerCast(clone, CB->getCalledOperand()->getType(), "", CB));
                        else
                            CB->setCalledFunction(clone);
                    // Otherwise plan a clone
                    } else {
                        // clone only if is a planned clone, otherwise leave as is
                        // NB: this assumes that all calls to `C` from `SCC`
                        // have been planned equally to be cloned or not, otherwise
                        // calls to `C` will not be consistent inside `SCC`
                        if (isPlannedClone(*CB) == false) continue;
                        cgcCallBaseQueue.push(CB);
                    }
                }
            }
        }
        return FtoClones[F];
    }

    // Clone the function `F`, and update the `cgcCallBaseQueue` to continue
    // the visit
    Function* addFunctionClone(CallBaseQueue &cgcCallBaseQueue, Function *F, long prio) {

        // The assertion is valid only if we visit the graph in BFS mode, i.e.
        // starting from a single root, in the general case we may revisit a function
        // that has been cloned, that now has two callers since his parent is cloned
        // assert(!isClone(F));

        // bail out if blacklisted
        if (isBlacklisted(F))
            return F;

        // bail out if cloning `F` would exceed the max size
        if (!allowedToClone(F))
            return F;

        if (isInSCC(F))
            return addSCCClone(cgcCallBaseQueue, F, prio);

        // Clone original function if required
        if (shouldCloneFunction(F)) {
            ValueToValueMapTy VMap;
            Function *clone = CloneFunction(F, VMap);
            assert(clone);
            updateMetadata(clone, F, VMap);
            trackClone(clone, cgcCallBaseQueue);

            setCloneName(clone);
            fixPrologue(clone, F);

            // Add the target to the functions to process.
            updateCallBaseQueue(cgcCallBaseQueue, clone);

            // Add the priority to the clone to keep track of it
            setFunctionPriority(clone, prio);

            return clone;
        } else {
            // Set the original function as a clone without updating the number of clones
            trackClone(F, cgcCallBaseQueue, /*update=*/false);
            // Add the target to the functions to process.
            updateCallBaseQueue(cgcCallBaseQueue, F);

            // Add the priority to the clone to keep track of it
            setFunctionPriority(F, prio);

            return F;
        }
    }

    // Visit the call base `CB` to clone its target
    void cgc(CallBase *CB, CallBaseQueue &cgcCallBaseQueue) {
        Function *F = CB->getFunction();

        // bail out if blacklisted
        if (isBlacklisted(F))
            return;

        // For direct calls, simply redirect target to new clone
        Function *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
        // this should not be an edge between two functions in the same SCC
        assert(!isInSCC(F) || !isInSCC(C) || (FunctionToSCC[F].find(C) == FunctionToSCC[F].end() 
            && FunctionToSCC[C].find(F) == FunctionToSCC[C].end()));
        if (C) {
            // clone only if is a planned clone, otherwise leave as is
            if (isPlannedClone(*CB) == false) return;
            long prio = getPriority(CB);
            Function *clone = addFunctionClone(cgcCallBaseQueue, C, prio);
            if (clone->getFunctionType() != CB->getCalledOperand()->getType()->getPointerElementType())
                CB->setCalledFunction(CB->getFunctionType(), CastInst::CreatePointerCast(clone, CB->getCalledOperand()->getType(), "", CB));
            else
                CB->setCalledFunction(clone);
        }
    }

    // Check if `F` just calls himself
    bool isSimplyRecursive(Function *F) {
        for (auto &BB : *F)
        for (auto &I : BB.instructionsWithoutDebug())
            if (auto *CB = dyn_cast<CallBase>(&I)) {
                Function *Callee = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                
                // Function calls itself
                if (Callee == F) {
                    return true;
                }
            }
        return false;
    }

    // Visit the `SCC` to gather the informations needed in `FunctionToSCC` and
    // `SCCFunctions`
    void collectSCC(CallGraphSCC &SCC) {
        std::set<Function *> Functions;
        for (CallGraphNode *I : SCC) {
            Functions.insert(I->getFunction());
        }

        // If the SCC contains multiple nodes we know there is recursion.
        if (Functions.size() != 1) {
            for (Function *F : Functions) {
                SCCFunctions.insert(F);
                assert(!F->doesNotRecurse());

                // A function should belong to a single SCC
                assert(FunctionToSCC.find(F) == FunctionToSCC.end());
                FunctionToSCC[F] = Functions;
            }
        // Take into account simple recursive functions
        } else {
            Function *F = *Functions.begin();
            if (F && isSimplyRecursive(F)) {
                SCCFunctions.insert(F);
                assert(!F->doesNotRecurse());

                assert(FunctionToSCC.find(F) == FunctionToSCC.end());
                FunctionToSCC[F] = Functions;
            }
        }
    }

    // Return true if `F` is blacklisted
    bool isBlacklisted(Function *F) {
        MDNode* N;
        N = F->getMetadata(CGC_CLONE_NEVER);
        if (N == NULL) return false;
        return true;
    }

    // Return true if `F` is part of a SCC
    bool isInSCC(Function *F) {
        return SCCFunctions.find(F) != SCCFunctions.end();
    }
    
    // Return true if `F` is a clone of a function
    bool isClone(Function *F) {
        return FunctionClones.find(F) != FunctionClones.end();
    }

    // Add `F` to the function clones we keep track of, and update stats
    void trackClone(Function *F, CallBaseQueue& cgcCallBaseQueue, bool update=true) {
        FunctionClones.insert(F);
        if (update) {
            ++nclones;
            aflmap_size += FunctionToAFLMapSize[F];
        }
        LLVM_DEBUG(dbgs() << "\r"  << nclones << " - " << aflmap_size << "              ");
    }

    // Sometimes LLVM build the CallGraph withouth taking into considerations calls
    // that pass through a `bitcast` operation. We fix this here, revisiting the
    // functions and updating the CallGraph
    void fixCallGraph(Module &M, CallGraph *CG) {
        for (auto &F : M.getFunctionList()) {
            if (F.isDeclaration() || isAvailableExternally(F))
                continue;
            for(auto &BB: F) {
                for (auto &I : BB) {
                    if (CallBase * CB = dyn_cast<CallBase>(&I)) {
                        if (CB->isInlineAsm()) continue;

                        Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                        if (!Called || Called->isDeclaration()  || isAvailableExternally(*Called)|| Called->isIntrinsic()) continue;

                        // If `Called` actually points to a function, but getCalledFunction
                        // returns null then we have spotted a missing function
                        if (CB->getCalledFunction() == nullptr) {
                            CallGraphNode *Node = CG->getOrInsertFunction(&F);
                            Node->addCalledFunction(CB, CG->getOrInsertFunction(Called));
                        }
                    }
                }
            }
        }
    }

    // Initialize the `FunctionToCallBases` structure with all the existing CallBases in `F`
    void gatherCallBases(Function *F) {
        // Initialize the set in case no call is present in the function
        FunctionToCallBases[F];
        for (BasicBlock &BB: *F) {
            for (Instruction &I : BB) {
                // Gather all call bases
                if (CallBase * CB = dyn_cast<CallBase>(&I)) {

                    // Only if they represent direct calls to functions
                    if (CB->isInlineAsm()) continue;
                    Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                    if (!Called || Called->isDeclaration() || isAvailableExternally(*Called) || Called->isIntrinsic()) continue;

                    // Insert into the map
                    FunctionToCallBases[F].insert(CB);
                }
            }
        }
    }

    // The optimizer may decide to inline functions and simplify them. Or directly simplify
    // static/internal ones. Try to persuade it to avoid simplifying functions we want as is,
    // by setting all the functions `F` calls to not static and not inlinable.
    void hardenFunction(Function *F) {
        for (BasicBlock &BB: *F) {
            for (Instruction &I : BB) {
                // Gather all call bases
                if (CallBase * CB = dyn_cast<CallBase>(&I)) {

                    // Only if they represent direct calls to functions
                    if (CB->isInlineAsm()) continue;
                    Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                    if (!Called || Called->isDeclaration() || isAvailableExternally(*Called) || Called->isIntrinsic()) continue;
                    
                    // Harden from inlining
                    if (Called->hasFnAttribute(Attribute::InlineHint))
                        Called->removeFnAttr(Attribute::InlineHint);
                    if (Called->hasFnAttribute(Attribute::AlwaysInline))
                        Called->removeFnAttr(Attribute::AlwaysInline);
                    Called->addFnAttr(Attribute::NoInline);

                    // Harden from static/internal-driven simplifications
                    GlobalValue *GVF = dyn_cast<GlobalValue>(Called);
                    GVF->setVisibility(GlobalValue::DefaultVisibility);
                    GVF->setLinkage(GlobalValue::ExternalLinkage);
                }
            }
        }
    }

    virtual bool runOnModule(Module &M) override {
        cgcPassLog("Running...");

        // Initialize regular expressions for functions to harden against optimizer
        std::vector<Regex*> HardenFunctionRegexes;
        if (HardenFunctions.empty()) {
            HardenFunctions.push_back("main");
            HardenFunctions.push_back("LLVMFuzzerTestOneInput");
        }
        passListRegexInit(HardenFunctionRegexes, HardenFunctions);

        CallGraph *CG = &getAnalysis<CallGraphWrapperPass>().getCallGraph();

        // LLVM does not consider edges like `call (bitcast (func))` so insert them.
        // really llvm??
        fixCallGraph(M, CG);

        // Walk the callgraph in bottom-up SCC order.
        scc_iterator<CallGraph*> CGI = scc_begin(CG);
        
        CallGraphSCC CurSCC(*CG, &CGI);
        while (!CGI.isAtEnd()) {
            // Copy the current SCC and increment past it so that the pass can hack
            // on the SCC if it wants to without invalidating our iterator.
            const std::vector<CallGraphNode *> &NodeVec = *CGI;
            CurSCC.initialize(NodeVec);
            ++CGI;
        
            collectSCC(CurSCC);
        }

        // Collect all functions in the module and add root function clones.
        CallBaseQueue cgcCallBaseQueue;
        std::set<Function*> HardenFunctionsSet;
        std::list<Function*> skippedFuncs;
        for (auto &F : M.getFunctionList()) {
            if (F.isDeclaration() || isAvailableExternally(F))
                continue;

            // gather all the call bases in the function
            gatherCallBases(&F);

            // gather the estimation for the AFL map size
            FunctionToAFLMapSize[&F] = estimateAFLEdges(&F);
            // update the current size
            aflmap_size += FunctionToAFLMapSize[&F];

            const std::string &FName = F.getName().str();
            if (passListRegexMatch(HardenFunctionRegexes, FName)) {
                HardenFunctionsSet.insert(&F);
            }
            if (!isCGCRoot(F)) {
                // keep track of the functions skipped
                if (!isInSCC(&F)) skippedFuncs.push_back(&F);
                // BUG: here if the scc is a root scc, you will never clone the callsited of the root SCC that go outside the SCC
                continue;
            }
            assert(!isInSCC(&F) && 
                "Cannot set a function belonging to an SCC as a root function to be cloned");
            updateCallBaseQueue(cgcCallBaseQueue, &F);
        }

        // Harden each function against the optimizer
        for (Function *F: HardenFunctionsSet)
            hardenFunction(F);
        
        // if the map size is already at the max, just return
        if (aflmap_size >= MaxSize) return true;

        // Start from root function clones and iteratively clone the callgraph.
        while (!cgcCallBaseQueue.empty()) {
            CallBase *CB = cgcCallBaseQueue.top();
            cgcCallBaseQueue.pop();
            cgc(CB, cgcCallBaseQueue);
            // `cgc` should never clone past the limit
            assert (aflmap_size <= MaxSize);
        }
        
        // now clone all the other calls if still have budget
        if (CGCFill && aflmap_size < MaxSize) {
            oprint("Finished planned clones, still continuing to clone");
            for (Function* F: skippedFuncs) {
                updateCallBaseQueue(cgcCallBaseQueue, F);
            }
            // restart the visit to clone all the remaining calls
            while (!cgcCallBaseQueue.empty()) {
                CallBase *CB = cgcCallBaseQueue.top();
                cgcCallBaseQueue.pop();
                cgc(CB, cgcCallBaseQueue);
                // `cgc` should never clone past the limit
                assert (aflmap_size <= MaxSize);
            }
        }

        // normalize names and mark all the clones
        for (Function *F: FunctionClones) {
            if (F->isDeclaration() || isAvailableExternally(*F))
                continue;
            normalizeName(F);
            markClone(F);
        }
        oprint("\nTotal Clones: " << nclones);
        return true;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
        AU.addRequired<CallGraphWrapperPass>();
        AU.addRequired<DominatorTreeWrapperPass>();
        AU.addRequired<PostDominatorTreeWrapperPass>();
    }
  };

}

char CallgraphClonePass::ID = 0;
RegisterPass<CallgraphClonePass> MP("cgc", "CallgraphClone Pass");
