
#include <pass.h>
#include "llvm/Analysis/CFG.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/ADT/SCCIterator.h"
#include "WPA/WPAPass.h"
#include "WPA/FlowSensitive.h"
#include "SVF-FE/PAGBuilder.h"
#include <cgc_magics.h>
#include <cstdlib>

using namespace llvm;
using namespace SVF;

#define DEBUG_TYPE "CallgraphClonePlanner"
#define CallgraphClonePlannerPassLog(M) LLVM_DEBUG(dbgs() << "CallgraphClonePlannerPass: " << M << "\n")
#define oprint(s) LLVM_DEBUG(outs() << s << "\n")
#define dprint(s) (outs() << s << "\n")

enum PlanningStrategy {
  bfs, bottom, uniform, randomic, dataflow
};

// The cloning strategy to follow when marking functions/calls to be cloned
cl::opt<PlanningStrategy> Strategy("cgc-strategy", cl::desc("The Callgraph Cloning strategy:"),
    cl::values(
        clEnumVal(bfs,   "clone everything starting from specified roots"),
        clEnumVal(bottom,   "clone everything starting from the leafs"),
        clEnumVal(uniform,   "clone everything uniformly"),
        clEnumVal(randomic, "clone random subgraphs of the Callgraph"),
        clEnumVal(dataflow, "clone uniformily with priorities depending on the expected improvement on dataflow diversity (using SVF)")
    ),
    cl::init(bfs)
);

static cl::list<std::string>
RootFunctions("cgc-funcs",
    cl::desc("Specify all root functions (for tree based strategies) as comma-separated function regexes"),
    cl::ZeroOrMore, cl::CommaSeparated, cl::NotHidden);

static cl::opt<unsigned>
CallsThreshold("cgc-calls-treshold", 
cl::init(0), cl::NotHidden,
cl::desc("The threshold of incoming calls for which a function is considered an error function and not prioritized\n\t[default: 0 -> set to treshold_factor*initial_number_of_funcs]"));

static cl::opt<float>
CallsThresholdFactor("cgc-calls-treshold-factor", 
cl::init(0.25), cl::NotHidden,
cl::desc("The threshold factor on which cgc-calls-treshold is computed if initialized to 0"));

static cl::opt<int>
RandomSeed("cgc-random-seed", 
cl::init(-1), cl::NotHidden,
cl::desc("Random seed\n\t[default: -1 -> get seed from time(0)"));


namespace {
  // This pass marks which functions and which CallBases should be cloned by CGC
  // pass according to different strategies
  class CallgraphClonePlannerPass : public ModulePass {

    // Root functions regexes to match
    std::vector<Regex*> FunctionRegexes;

    // All the functions that should not be cloned, however planner can decide 
    // what to do with these functions
    std::set<Function*> FunctionBlacklist;

    // The number of times a function is originally called
    std::map<Function*, unsigned long> CallsToFunction;

    // Keep track of all the functions belonging to strongly connected components
    std::set<Function*> SCCFunctions;
    std::map<Function*, std::set<Function*>> FunctionToSCC;

    // A set of objects
    using ObjSet = std::set<const Value*>;

    // CallBase to an object set to which the params may point to
    using CallBase2ParamObjs = std::map<CallBase*, ObjSet>;

    // For each function, for each callbase, keep track of the object that the params may point to
    using Function2CallBaseParamObjs = std::map<Function*, CallBase2ParamObjs>;

    // Return true if `F` has an available_externally linkage (i.e. equivalent to a declaration)
    bool isAvailableExternally(Function &F) {
        GlobalValue::LinkageTypes L = F.getLinkage();
        return GlobalValue::isAvailableExternallyLinkage(L);
    }

    void planRoot(Function &F) {
        assert(!isInSCC(&F) && "Cannot plan F as root, since is in a SCC");
        LLVMContext& C = F.getContext();
        MDNode* N = MDNode::get(C, ConstantAsMetadata::get(ConstantInt::get(C, APInt(sizeof(unsigned long)*8, 1, true))));
        F.setMetadata(CGC_ROOT_ATTR, N);
    }

    void planClone(CallBase &CB) {
        LLVMContext& C = CB.getContext();
        MDNode* N = MDNode::get(C, ConstantAsMetadata::get(ConstantInt::get(C, APInt(sizeof(unsigned long)*8, 1, true))));
        CB.setMetadata(CGC_CLONE_CALL_ATTR, N);
    }

    void setPriority(CallBase &CB, long prio) {
        LLVMContext& C = CB.getContext();
        MDNode* N = MDNode::get(C, ConstantAsMetadata::get(ConstantInt::get(C, APInt(sizeof(unsigned long)*8, prio, true))));
        CB.setMetadata(CGC_CLONE_PRIORITY, N);
    }

    void setBlacklistedMetadata(Function &F) {
        LLVMContext& C = F.getContext();
        MDNode* N = MDNode::get(C, ConstantAsMetadata::get(ConstantInt::get(C, APInt(sizeof(unsigned long)*8, 1, true))));
        F.setMetadata(CGC_CLONE_NEVER, N);
    }

    // Set the root function required, and set all calls in the callgraph to
    // be cloned with the same priority. Blacklisted functions get priority 0.
    // This makes CGC clone in a BFS fashion starting from the roots.
    void bfsPlanner(Module &M) {
        for (Function &F: M) {
            if (F.isDeclaration() || isAvailableExternally(F))
                continue;
            
            // set metadata if root function
            const std::string &FName = F.getName().str();
            if (passListRegexMatch(FunctionRegexes, FName)) planRoot(F);

            // clone all calls in the callgraph
            for (BasicBlock &BB: F) {
                for (Instruction &I: BB) {
                    // Search all call bases
                    if (CallBase * CB = dyn_cast<CallBase>(&I)) {

                        // Only if they represent direct calls to functions
                        if (CB->isInlineAsm()) continue;
                        Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                        if (!Called || Called->isDeclaration() || isAvailableExternally(*Called) || Called->isIntrinsic()) continue;

                        planClone(*CB);
                        if (isBlacklisted(Called)) {
                            setPriority(*CB, 0);
                            // still give a possibility to the function and do not blacklist it
                            // setBlacklistedMetadata(*Called);
                        } else {
                            setPriority(*CB, 1);
                        }
                    }
                }
            }
        }
    }

    // Set all functions as root function, and set all calls in the callgraph to
    // be cloned with the same priority. Blacklisted functions get priority 0.
    // This makes CGC clone all the functions equally until the maximum size.
    void uniformPlanner(Module &M) {
        for (Function &F: M) {
            if (F.isDeclaration() || isAvailableExternally(F))
                continue;
            
            // set metadata for all functions that are not in a SCC, since they 
            // cannot be a root
            if (!isInSCC(&F)) planRoot(F);

            // clone all calls in the callgraph
            for (BasicBlock &BB: F) {
                for (Instruction &I: BB) {
                    // Search all call bases
                    if (CallBase * CB = dyn_cast<CallBase>(&I)) {

                        // Only if they represent direct calls to functions
                        if (CB->isInlineAsm()) continue;
                        Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                        if (!Called || Called->isDeclaration() || isAvailableExternally(*Called) || Called->isIntrinsic()) continue;

                        planClone(*CB);
                        if (isBlacklisted(Called)) {
                            setPriority(*CB, 0);
                            // still give a possibility to the function and do not blacklist it
                            // setBlacklistedMetadata(*Called);
                        } else {
                            setPriority(*CB, 1);
                        }
                    }
                }
            }
        }
    }

    // Set all functions as root function, and set all calls in the callgraph to
    // be cloned with a priority based on the call depth of the function wrt to the root. 
    // Blacklisted functions get priority 0.
    // This makes CGC clone all the functions in a bottom-up fashion until the maximum size.
    void bottomPlanner(Module &M) {
        std::list<Function*> toVisit;
        std::set<Function*> visited;

        // keep track of bfs layer
        long bfs_order = 1;
        for (Function &F: M) {
            if (F.isDeclaration() || isAvailableExternally(F))
                continue;

            // start from root
            const std::string &FName = F.getName().str();
            if (passListRegexMatch(FunctionRegexes, FName)) toVisit.push_back(&F);
        }

        while (!toVisit.empty()) {
            // Get a function to visit
            Function *F = toVisit.front();
            toVisit.pop_front();

            // If function already visited continue
            if (visited.find(F) != visited.end()) continue;
            visited.insert(F);

            // set metadata for all functions that are not in a SCC, since they 
            // cannot be a root
            if (!isInSCC(F)) planRoot(*F);

            // clone all calls in the callgraph
            for (BasicBlock &BB: *F) {
                for (Instruction &I: BB) {
                    // Search all call bases
                    if (CallBase * CB = dyn_cast<CallBase>(&I)) {

                        // Only if they represent direct calls to functions
                        if (CB->isInlineAsm()) continue;
                        Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                        if (!Called || Called->isDeclaration() || isAvailableExternally(*Called) || Called->isIntrinsic()) continue;

                        planClone(*CB);
                        if (isBlacklisted(Called)) {
                            setPriority(*CB, 0);
                            // still give a possibility to the function and do not blacklist it
                            // setBlacklistedMetadata(*Called);
                        } else {
                            setPriority(*CB, bfs_order);
                        }

                        // insert the target function to be visited
                        toVisit.push_back(Called);
                    }
                }
            }
            // increment the bfs layer at each visited call
            ++bfs_order;
        }

        // Plan all the others function that we did not reach with the visit (i.e. indirect calls)
        // assume they are all at `bfs_order/2` (totally arbitrary sorry)
        for (Function &F: M) {

            if (F.isDeclaration() || isAvailableExternally(F))
                continue;

            // If function already visited continue
            if (visited.find(&F) != visited.end()) continue;
            visited.insert(&F);

            if (!isInSCC(&F)) planRoot(F);

            for (BasicBlock &BB: F) {
                for (Instruction &I: BB) {
                    // Search all call bases
                    if (CallBase * CB = dyn_cast<CallBase>(&I)) {

                        // Only if they represent direct calls to functions
                        if (CB->isInlineAsm()) continue;
                        Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                        if (!Called || Called->isDeclaration() || isAvailableExternally(*Called) || Called->isIntrinsic()) continue;

                        planClone(*CB);
                        if (isBlacklisted(Called)) {
                            setPriority(*CB, 0);
                            // still give a possibility to the function and do not blacklist it
                            // setBlacklistedMetadata(*Called);
                        } else {
                            setPriority(*CB, bfs_order/2);
                        }
                    }
                }
            }
        }
    }

    // Simple static dataflow analysis from V to its users, collecting all the values
    // that may depend on V
    std::set<Value*> collectAllDependentValues(Value* V) {
        static std::map<Value*, std::set<Value*>> dependentValuesCache;

        if (dependentValuesCache.find(V) != dependentValuesCache.end()) {
            return dependentValuesCache[V];
        }

        std::set<Value*> &dependentValues = dependentValuesCache[V];
        std::list<Value *> toVisit;

        // initialize structs
        toVisit.push_back(V);
        dependentValues.insert(V);

        while (!toVisit.empty()) {
            Value *curr = toVisit.front();
            toVisit.pop_front();
            for (Value* user: curr->users()) {
                if (dependentValues.find(user) == dependentValues.end()) {
                    dependentValues.insert(user);
                    toVisit.push_back(user);
                }
            }

            // forward data flow through memory in a naive way
            if (StoreInst *SI = dyn_cast<StoreInst>(curr)) {
                // taint the pointer operand
                Value *ptr = SI->getPointerOperand();
                if (dependentValues.find(ptr) == dependentValues.end()) {
                    dependentValues.insert(ptr);
                    toVisit.push_back(ptr);
                }
            }
        }
        return dependentValues;
    }

    // Returns all allocation sites from which V might have originated in F.
    // Simple static dataflow analysis from V up to the values it depends on
    std::set<Value*>  getAllocSites(Value *V, const Function &F) {
        static std::map<Value*, std::set<Value*>> allocCache;

        if (allocCache.find(V) != allocCache.end()) {
            return allocCache[V];
        }

        std::set<Value*> &allocs = allocCache[V];
        std::list<Value *> toVisit;
        std::set<Value *> visited;

        // initialize structs
        toVisit.push_back(V);

        while (!toVisit.empty()) {
            Value *curr = toVisit.front();
            toVisit.pop_front();
            if (visited.find(curr) != visited.end()) continue;
            visited.insert(curr);

            if (isa<AllocaInst>(curr) || isa<GlobalValue>(curr)) {
                // Add alloca and globals
                allocs.insert(curr);
            } else if (isa<CallBase>(curr)) {
                // if it is a call, and it is a pointer type, assume is some sort
                // of allocation, and add it to the output
                if (!curr->getType()->isPointerTy()) continue;
                allocs.insert(curr);
            } else if (User *currU = dyn_cast<User>(curr)) {
                for (Value *operand: currU->operands()) {
                    toVisit.push_back(operand);
                }
            } else {
                // if it is not an instruction, may be an argument (or something else?)
                // add to the alloc sites
                // dprint(*curr);
                allocs.insert(curr);
            }
        }
        return allocs;
    }

    // Add all the objects that the params of CB may points-to, to `PossibleObjs`
    void collectParamObjects(CallBase *CB, ObjSet &PossibleObjs) {
        Function *F = CB->getFunction();
        // collect all the possible target object of params passed by the callbase
        for (Value* arg: CB->args()) {
            if (!arg->getType()->isPointerTy()) continue;

            for (const Value* alloc: getAllocSites(arg, *F)) {
                // oprint("     A: " << *alloc);
                // add the object to the output
                PossibleObjs.insert(alloc);
            }
        }
    }

    // Choose a random sized, random set of root functions, each with random priorities
    // for each call. Blacklisted functions get priority 0.
    void randomicPlanner(Module &M) {
        // Random but need to take into account SCCs, since all clones to the same
        // function in the SCC should be planned the same, otherwise the size estimation
        // of the SCC clone will be wrong

        // Compute the total number of functions, excluding the ones in an SCC
        unsigned int numFunctions = 0;
        for (Function &F: M) {
            if (F.isDeclaration() || isAvailableExternally(F))
                continue;
            
            // ignore the ones in a SCC
            if (isInSCC(&F)) continue;
            ++numFunctions;
        }

        // The number of functions to set as roots
        unsigned int numRoots = rand() % numFunctions + 1;
        
        for (Function &F: M) {
            if (F.isDeclaration() || isAvailableExternally(F))
                continue;
            
            // set as root all functions that are not in a SCC, with probability 1/numRoots
            if (!isInSCC(&F) && (rand() % numRoots == 0)) planRoot(F);

            // clone all calls in the callgraph
            for (BasicBlock &BB: F) {
                for (Instruction &I: BB) {
                    // Search all call bases
                    if (CallBase * CB = dyn_cast<CallBase>(&I)) {

                        // Only if they represent direct calls to functions
                        if (CB->isInlineAsm()) continue;
                        Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                        if (!Called || Called->isDeclaration() || isAvailableExternally(*Called) || Called->isIntrinsic()) continue;

                        planClone(*CB);
                        if (isBlacklisted(Called)) {
                            setPriority(*CB, 0);
                            // still give a possibility to the function and do not blacklist it
                            // setBlacklistedMetadata(*Called);
                        } else {
                            // set a random priority from 1 to 100
                            setPriority(*CB, (rand() % 100) + 1);
                        }
                    }
                }
            }
        }
    }
    
    // Add all the objects that the params of CB may points-to, to `PossibleObjs`
    void collectSVFParamObjects(PointerAnalysis* pta, CallBase *CB, ObjSet &PossibleObjs) {
        assert(pta);
        // collect all the possible target object of params passed by the callbase
        for (Value* arg: CB->args()) {
            if (!arg->getType()->isPointerTy()) continue;

            NodeID pNodeId = pta->getPAG()->getValueNode(arg);
            const NodeBS& pts = pta->getPts(pNodeId);
            for (NodeBS::iterator ii = pts.begin(), ie = pts.end(); ii != ie; ii++) {
                PAGNode* targetObj = pta->getPAG()->getPAGNode(*ii);

                // Ensure we do not deal with dummy or const objects
                if(!targetObj->hasValue()) continue;
                const Value* targetObjVal = targetObj->getValue();
                
                // add the object to the output
                PossibleObjs.insert(targetObjVal);
            }
        }
    }

    // Return the weight for a CallBase, based on its dataflow diversity
    long getWeightForDataflow(CallBase *CB, CallBase2ParamObjs &ParamObjPerCall) {
        long weight = 0;
        assert(ParamObjPerCall.find(CB) != ParamObjPerCall.end());
        // the number of different calls to CB->target
        int numberOfContexts = ParamObjPerCall.size();

        // count how many contexts access an object
        std::map<const llvm::Value *, int> objCount;
        for (const std::pair<CallBase *const, std::set<const Value *>> &CallBaseAndPossibleObjs: ParamObjPerCall) {
            auto & possibleObjs = CallBaseAndPossibleObjs.second;
            for (const llvm::Value *obj: possibleObjs) {
                objCount[obj]++;
            }
        }

        // for each object accessed by `CB`, add 1 for each context where it is not accessed (so unique objs weight more)
        for (const Value *obj: ParamObjPerCall[CB]) {
            // const Value* obj = pair.first;
            assert(objCount.find(obj) != objCount.end());
            int count = objCount[obj];
            weight += (numberOfContexts - count);
        }

        // normalize on number of calling contexts
        return (weight * 100) / numberOfContexts;
    }

    void dumpPtsObjects(Function2CallBaseParamObjs &ParamObjPerCallPerFunction) {
        // recreate the map but using strings to have a sorted visit
        // super lazy inefficient way
        // std::map<llvm::Function *, std::map<llvm::CallBase *, std::set<const llvm::Value *>>> sorted;
        std::map   <std::string,      std::map<std::string,      std::set<      std::string>>> sorted;
        for (auto &pair: ParamObjPerCallPerFunction) {
            Function *F = pair.first;
            std::string FName = F->getName(); 
            CallBase2ParamObjs &callBase2Objs = pair.second;
            for (auto &pair: callBase2Objs) {
                CallBase *CB = pair.first;
                std::string CBStr;
                llvm::raw_string_ostream rso(CBStr);
                CB->print(rso);
                ObjSet &objs = pair.second;
                for (auto &obj: objs) {
                    // if global value the name is sufficient
                    if (isa<GlobalValue>(obj)) {
                        sorted[FName][CBStr].insert(obj->getName());
                        continue;
                    }
                    std::string OStr;
                    llvm::raw_string_ostream rso(OStr);
                    obj->print(rso);
                    sorted[FName][CBStr].insert(OStr);
                }
            }
        }
        for (auto &pair: sorted) {
            const std::string &FName = pair.first;
            dprint(FName);
            for (auto &pair1: pair.second) {
                const std::string &CBStr = pair1.first;
                dprint("- " << CBStr);
                for (const std::string &objStr: pair1.second) {
                    dprint("    - " << objStr);
                }
            }
        }
    }

    // Set all functions as root function, and set all calls in the callgraph to
    // be cloned with a priority based on the expected dataflow improvement.
    // Blacklisted functions get priority 0.
    // This makes CGC clone all the functions equally until the maximum size.
    void dataflowPlanner(Module &M, PointerAnalysis *pta) {
        assert((pta) && "At least a pointer analysis wrapper must be used");

        // keep track of all the object that may be passed from different callbases to the same function
        Function2CallBaseParamObjs ParamObjPerCallPerFunction;

        // collect all the objects accessed by fuctions given their calling context
        for (Function &F: M) {
            for (BasicBlock &BB: F) {
                for (Instruction &I: BB) {
                    // Search all call bases
                    if (CallBase * CB = dyn_cast<CallBase>(&I)) {

                        // Only if they represent direct calls to functions
                        if (CB->isInlineAsm()) continue;
                        Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                        if (!Called || Called->isDeclaration() || isAvailableExternally(*Called) || Called->isIntrinsic()) continue;

                        if (isBlacklisted(Called)) continue;

                        // Collect the object the parameters may point-to
                        if (pta)
                            collectSVFParamObjects(pta, CB, ParamObjPerCallPerFunction[Called][CB]);
                    }
                }
            }
        }

        // print all the object for each function callsite
        // dumpPtsObjects(ParamObjPerCallPerFunction);

        // Now assign weights to calls based on the collected objects
        for (Function &F: M) {
            if (F.isDeclaration() || isAvailableExternally(F))
                continue;
            
            // set metadata for all functions that are not in a SCC, since they 
            // cannot be a root
            if (!isInSCC(&F)) planRoot(F);

            // clone all calls in the callgraph
            for (BasicBlock &BB: F) {
                for (Instruction &I: BB) {
                    // Search all call bases
                    if (CallBase * CB = dyn_cast<CallBase>(&I)) {

                        // Only if they represent direct calls to functions
                        if (CB->isInlineAsm()) continue;
                        Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                        if (!Called || Called->isDeclaration() || isAvailableExternally(*Called) || Called->isIntrinsic()) continue;

                        planClone(*CB);
                        if (isBlacklisted(Called)) {
                            setPriority(*CB, 0);
                            // still give a possibility to the function and do not blacklist it
                            // setBlacklistedMetadata(*Called);
                        } else {
                            assert(ParamObjPerCallPerFunction.find(Called) != ParamObjPerCallPerFunction.end());
                            long weight = getWeightForDataflow(CB, ParamObjPerCallPerFunction[Called]);
                            // add 1 so higher priority than blacklisted anyway
                            setPriority(*CB, weight + 1);
                        }
                    }
                }
            }
        }
    }

    // Visit `F` and all the functions called by `F`, adding them to `visitedFuncs`
    void visitCalledFunctions(Function* F, std::set<Function*> &visitedFuncs) {
        // bail out if already visited
        if (visitedFuncs.find(F) != visitedFuncs.end()) return;

        // insert into the visited functions
        visitedFuncs.insert(F);

        for (auto &BB : *F)
        for (auto &I : BB) {
            if (CallBase * CB = dyn_cast<CallBase>(&I)) {
                if (CB->isInlineAsm()) continue;

                Function *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                if (C) {
                    if (C->isDeclaration() || isAvailableExternally(*C) || C->isIntrinsic())
                    continue;
                    visitCalledFunctions(C, visitedFuncs);
                }
            }
        }
    }

    // Update info on the functions called
    void gatherCallInfo(Function *F) {
        for (BasicBlock &BB: *F) {
            for (Instruction &I : BB) {
                // Gather all call bases
                if (CallBase * CB = dyn_cast<CallBase>(&I)) {

                    // Only if they represent direct calls to functions
                    if (CB->isInlineAsm()) continue;
                    Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                    if (!Called || Called->isDeclaration() || isAvailableExternally(*Called) || Called->isIntrinsic()) continue;

                    // Update the info on number of times a function is called
                    CallsToFunction[Called]++;
                }
            }
        }
    }

    // Return true if `F` is blacklisted
    bool isBlacklisted(Function *F) {
        return FunctionBlacklist.find(F) != FunctionBlacklist.end();
    }

    // Try to match uninteresting functions, like allocs and free, which usually
    // have varying dataflow which is however uninteresting
    bool isUninteresting(Function* F) {
        if (F->getName().contains_lower("alloc")) return true;
        if (F->getName().contains_lower("free")) return true;
        if (F->getName().contains_lower("init")) return true;
        return false;
    }

    // Add the function `F` to the blacklist if the number of calls to it is higher
    // than the user threshold. If `F` belong to a SCC, add the SCC to the blacklist
    void maybeAddToBlacklist(Function *F) {

        // if already in the blacklist bail out
        if (isBlacklisted(F))
            return;

        // get the number of times `F` is called
        unsigned long numCalls = CallsToFunction[F];

        if (numCalls > CallsThreshold || isUninteresting(F)) {

            // if the function was in a SCC add all the functions
            if (isInSCC(F)) {
                assert(FunctionToSCC.find(F) != FunctionToSCC.end());
                for (Function *sccF: FunctionToSCC[F]) {
                    oprint("[-] excluding " << sccF->getName().str() << " due to " << F->getName().str() << " with " << numCalls << " calls");
                    FunctionBlacklist.insert(sccF);
                }
            // otherwise add just the function
            } else {
                oprint("[-] excluding " << F->getName().str() << " with " << numCalls << " calls");
                FunctionBlacklist.insert(F);
            }
        }
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
                        if (!Called || Called->isDeclaration() || isAvailableExternally(*Called) || Called->isIntrinsic()) continue;

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

    // Return true if `F` is part of a SCC
    bool isInSCC(Function *F) {
        return SCCFunctions.find(F) != SCCFunctions.end();
    }

  public:
    static char ID;
    CallgraphClonePlannerPass() : ModulePass(ID) {}

    virtual bool runOnModule(Module &M) override {

        // Initialize regular expressions for functions roots.
        if (RootFunctions.empty())
            RootFunctions.push_back("^main$");
        passListRegexInit(FunctionRegexes, RootFunctions);

        // Initialize RandomSeed if necessary
        if (RandomSeed == -1) RandomSeed = time(0);
        srand(RandomSeed);

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

        // Gather initial info on functions
        std::set<Function*> visitedFuncs;
        for (Function &F : M) {
            if (F.isDeclaration() || isAvailableExternally(F))
                continue;

            // count all the calls in the function
            gatherCallInfo(&F);
            const std::string &FName = F.getName().str();
            if (passListRegexMatch(FunctionRegexes, FName))
                continue;

            // visit the path starting from F and count called functions
            visitCalledFunctions(&F, visitedFuncs);
        }

        // Keep track of the initial number of functions used in the call path
        unsigned long initialNfuncs = visitedFuncs.size();

        // if CallsThreshold==0 automatically tune based on the number of functions
        if (CallsThreshold == 0) {
            CallsThreshold = CallsThresholdFactor * initialNfuncs;
            oprint("Threshold for error functions: " << CallsThreshold);
        }

        // Now revisit all the functions to fill the blacklist
        for (auto &F : M.getFunctionList()) {
            if (F.isDeclaration() || isAvailableExternally(F))
                continue;
        
            // fill the function black list if we detect it as an error function
            maybeAddToBlacklist(&F);
        }

        switch (Strategy)
        {
        case PlanningStrategy::bfs: {
            bfsPlanner(M);
            break;
        }

        case PlanningStrategy::uniform: {
            uniformPlanner(M);
            break;
        }

        case PlanningStrategy::bottom: {
            bottomPlanner(M);
            break;
        }


        case PlanningStrategy::randomic: {
            randomicPlanner(M);
            break;
        }
        
        case PlanningStrategy::dataflow: {
            SVFModule* svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(M);
            PAGBuilder builder;
            PAG* pag = builder.build(svfModule);

            FlowSensitive *pta = new FlowSensitive(pag);
            pta->analyze();
            dataflowPlanner(M, pta);
            break;
        }

        default:
            assert(false && "Clone strategy not supported");
            break;
        }
        return true;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
        AU.addRequired<CallGraphWrapperPass>();
        AU.addRequired<DominatorTreeWrapperPass>();
        AU.addRequired<PostDominatorTreeWrapperPass>();
    }
  };

}

char CallgraphClonePlannerPass::ID = 0;
RegisterPass<CallgraphClonePlannerPass> MP("cgc-planner", "CallgraphClonePlanner Pass");
