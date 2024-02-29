
#include <pass.h>

#include "llvm/IR/Module.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/CallGraphSCCPass.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/IR/CFG.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Utils/CodeExtractor.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/LoopInfo.h"
#include <set>
using namespace llvm;

#define DEBUG_TYPE "set-norecurse-ext"
#define setNoRecursExtPassLog(M) LLVM_DEBUG(dbgs() << "setNoRecursExtPass: " << M << "\n")

#define oprint setNoRecursExtPassLog

typedef long imd_t;

// This pass sets the norecurse attribute to all the external functions that we
// can guess they not recurse back to the program in any way.
// Since we are calling an external function the only way they could recurse back 
// in the module, or call a recursive function in it, is by
// passing a callback pointer to them, so check that
namespace {

  class SetNoRecursExtPass : public ModulePass {

  public:
    static char ID;
    SetNoRecursExtPass() : ModulePass(ID) {
    }

    bool  isFunctionPointerType(Type *type){
        // Check the type here
        if(PointerType *pointerType=dyn_cast<PointerType>(type)){
            return isFunctionPointerType(pointerType->getElementType());
        }
            //Exit Condition
            else if(type->isFunctionTy()){
            return  true;
            }
        return false;
    }

    void setNoRecursExt(CallSite &CS, Function *F) {
        oprint("Checking " << *CS.getInstruction());
        
        // Check no parameter is a function pointer
        for (auto &arg: F->args()) {
            Type* argT = arg.getType();
            oprint("  " << *argT);
            if (isFunctionPointerType(argT)) {
                oprint("  [-] not adding attr norecurse");
                return;
            }
        }
        oprint(" Callsite " << F->getName().str());
        // Check also the callsite
        for (auto &arg: CS.args()) {
            Type* argT = (*arg).getType();
            oprint("  " << *argT);
            if (isFunctionPointerType(argT)) {
                oprint("  [-] not adding attr norecurse");
                return;
            }
        }
        oprint("  [+] adding attr norecurse");
        // if check ok set the norecurse attrs
        if (!CS.hasFnAttr(Attribute::NoRecurse))
            CS.addAttribute(AttributeList::FunctionIndex, Attribute::NoRecurse);
        if (!F->hasFnAttribute(Attribute::NoRecurse))
            F->addFnAttr(Attribute::NoRecurse);
    }


    static bool addNoRecurseAttrs(CallGraphSCC &SCC) {
        SmallVector<Function *, 8> Functions;
        for (CallGraphNode *I : SCC) {
            Functions.push_back(I->getFunction());
        }
        
        // If the SCC contains multiple nodes we know for sure there is recursion.
        if (Functions.size() != 1)
            return false;

        Function *F = *Functions.begin();
        if (!F || !F->hasExactDefinition() || F->doesNotRecurse())
            return false;

        // If all of the calls in F are identifiable and are to norecurse functions, F
        // is norecurse. This check also detects self-recursion as F is not currently
        // marked norecurse, so any called from F to F will not be marked norecurse.
        for (auto &BB : *F)
        for (auto &I : BB.instructionsWithoutDebug())
            if (auto *CB = dyn_cast<CallBase>(&I)) {
                Function *Callee = dyn_cast<Function>(CB->getCalledValue()->stripPointerCasts());
                if (!Callee || Callee == F || !Callee->doesNotRecurse()) {
                    // Function calls a potentially recursive function.

                    // Check if the callsite has no recurse information
                    CallSite CS(&I);
                    if (!Callee && CS) continue;

                    return false;
                }
            }

        // Every call was to a non-recursive function other than this function, and
        // we have no indirect recursion as the SCC size is one. This function cannot
        // recurse.
        F->setDoesNotRecurse();
        return true;
    }

    virtual bool runOnModule(Module &M) override {
        setNoRecursExtPassLog("Running...");

        /* Iterate all functions in the module */
        for (auto &F : M.getFunctionList()) {
            if (F.isDeclaration())
                continue;
            for (auto &BB: F) {
                for (auto &I: BB) {
                    CallSite CS(&I);
                    if (!CS.getInstruction() || CS.isInlineAsm())
                        continue; // not a call
                    Function *Callee = dyn_cast<Function>(CS.getCalledValue()->stripPointerCasts());
                    if (!Callee)
                        continue; // not a direct call
                    
                    // if external function try to set the norecurse attr
                    if (Callee->isDeclaration())
                        setNoRecursExt(CS, Callee);
                }
            }
        }

        // Now visit the whole call graph in post order to derive norecurse attributes
        CallGraph *CG = &getAnalysis<CallGraphWrapperPass>().getCallGraph();
        // Walk the callgraph in bottom-up SCC order.
        scc_iterator<CallGraph*> CGI = scc_begin(CG);
        
        CallGraphSCC CurSCC(*CG, &CGI);
        while (!CGI.isAtEnd()) {
            // Copy the current SCC and increment past it so that the pass can hack
            // on the SCC if it wants to without invalidating our iterator.
            const std::vector<CallGraphNode *> &NodeVec = *CGI;
            CurSCC.initialize(NodeVec);
            ++CGI;
        
            addNoRecurseAttrs(CurSCC);
        }
        return true;
    }
 
   void getAnalysisUsage(AnalysisUsage &AU) const override {
        AU.addRequired<CallGraphWrapperPass>();
    }
  };

}

char SetNoRecursExtPass::ID = 0;
RegisterPass<SetNoRecursExtPass> MP("set-norecurse-ext", "Set NoRecurse Attr to external functions Pass");
