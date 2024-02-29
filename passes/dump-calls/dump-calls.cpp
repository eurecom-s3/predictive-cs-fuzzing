
#include <pass.h>
#include <cgc_magics.h>
#include <iostream>
#include <fstream>
#include <unistd.h>
#include "llvm/IR/IRBuilder.h"

using namespace llvm;

#define DEBUG_TYPE "DumpCalls"
#define DumpCallsPassLog(M) LLVM_DEBUG(dbgs() << "DumpCallsPass: " << M << "\n")
#define oprint(s) outs() << s << "\n"

namespace {

  // Dump the subtree of the CFG functions starting from `call-tree-start`
  class DumpCallsPass : public ModulePass {

  public:
    static char ID;
    DumpCallsPass() : ModulePass(ID) {}

    // Return true if `F` has an available_externally linkage (i.e. equivalent to a declaration)
    bool isAvailableExternally(Function &F) {
        GlobalValue::LinkageTypes L = F.getLinkage();
        return GlobalValue::isAvailableExternallyLinkage(L);
    }

    // Return whether the function has been marked as a clone
    static bool hasCloneMark(Function *F) {
        MDNode* N;
        assert(F);
        N = F->getMetadata(CGC_CLONE_MARK);
        if (N == NULL) return false;
        return true;
    }

    void createPrintCall(Module &M, Function &F, const std::string &to_print, const std::string &prefix, const std::string &suffix, IRBuilder<> &builder) {
        auto &CTX = M.getContext();
        PointerType *PrintfArgTy = PointerType::getUnqual(Type::getInt8Ty(CTX));

        // STEP 1: Inject the declaration of printf
        // ----------------------------------------
        // Create (or _get_ in cases where it's already available) the following
        // declaration in the IR module:
        //    declare i32 @printf(i8*, ...)
        // It corresponds to the following C declaration:
        //    int printf(char *, ...)
        FunctionType *PrintfTy = FunctionType::get(
            IntegerType::getInt32Ty(CTX),
            PrintfArgTy,
            /*IsVarArgs=*/true);

        FunctionCallee Printf = M.getOrInsertFunction("printf", PrintfTy);

        // Set attributes as per inferLibFuncAttributes in BuildLibCalls.cpp
        Function *PrintfF = dyn_cast<Function>(Printf.getCallee());
        PrintfF->setDoesNotThrow();
        PrintfF->addParamAttr(0, Attribute::NoCapture);
        PrintfF->addParamAttr(0, Attribute::ReadOnly);

        // STEP 2: Inject a global variable that will hold the printf format string
        // ------------------------------------------------------------------------
        llvm::Constant *PrintfFormatStr = llvm::ConstantDataArray::getString(
            CTX, prefix + to_print + suffix);

        Constant *PrintfFormatStrVar =
            M.getOrInsertGlobal(to_print, PrintfFormatStr->getType());
        dyn_cast<GlobalVariable>(PrintfFormatStrVar)->setInitializer(PrintfFormatStr);

        // Printf requires i8*, but PrintfFormatStrVar is an array: [n x i8]. Add
        // a cast: [n x i8] -> i8*
        llvm::Value *FormatStrPtr =
            builder.CreatePointerCast(PrintfFormatStrVar, PrintfArgTy, "formatStr");

        // Finally, inject a call to printf
        builder.CreateCall(
            Printf, {FormatStrPtr});
    }

    void visit(Function* F) {
      for (auto &BB : *F)
        for (auto &I : BB.instructionsWithoutDebug()) {
            if (CallBase * CB = dyn_cast<CallBase>(&I)) {
                if (CB->isInlineAsm()) continue;

                Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                if (!Called || Called->isDeclaration()  || isAvailableExternally(*Called)|| Called->isIntrinsic()) continue;

                // add the logging call
                IRBuilder<> IBuilder(&I);
                const std::string &to_print = Called->getName().str();
                if (hasCloneMark(Called))
                    createPrintCall(*F->getParent(), *F, CGC_CLONE_MARK + to_print, ">>> |", "\n", IBuilder);
                else
                    createPrintCall(*F->getParent(), *F, to_print, ">>> |", "\n", IBuilder);
            }
        }
    }

    virtual bool runOnModule(Module &M) {
        for (auto &F : M.getFunctionList()) {
            if (F.isDeclaration() || isAvailableExternally(F)) continue;
            visit(&F);
        }

        return true;
    }
  };

}

char DumpCallsPass::ID = 0;
RegisterPass<DumpCallsPass> MP("dump-calls", "DumpCalls Pass");

