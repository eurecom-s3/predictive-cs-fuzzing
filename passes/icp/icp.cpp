
#include <pass.h>
#include "WPA/WPAPass.h"
#include "llvm/Transforms/Utils/CallPromotionUtils.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"

using namespace llvm;
using namespace SVF;

#define DEBUG_TYPE "icp"
#define icpPassLog(M) LLVM_DEBUG(dbgs() << "ICPPass: " << M << "\n")
#define oprint(s) (dbgs() << s << "\n")
#define print(s) (errs() << s << "\n")

static cl::list<std::string>
Functions("icp-funcs",
    cl::desc("Specify all the comma-separated function regexes to icp"),
    cl::ZeroOrMore, cl::CommaSeparated, cl::NotHidden);

static cl::opt<bool>
VarArgOnly("icp-vararg-only",
    cl::desc("ICP only variadic calls"),
    cl::init(false), cl::NotHidden);

static cl::opt<bool>
Fallback("icp-fallback",
    cl::desc("Leave a fallback indirect call behind"),
    cl::init(false), cl::NotHidden);

static cl::opt<bool>
Abort("icp-abort",
    cl::desc("Leave an abort call for the default case"),
    cl::init(false), cl::NotHidden);

static cl::opt<bool>
TypeAnalysis("icp-type",
    cl::desc("Use faster type-based points-to analysis."),
    cl::init(false), cl::NotHidden);

static cl::opt<bool>
TypeAnalysisOpaquePtrs("icp-type-opaque-ptrs",
    cl::desc("Allow arbitrary ptr casts in type-based points-to analysis."),
    cl::init(true), cl::NotHidden);

static cl::opt<bool>
StrictSignature("icp-type-strict-signature",
    cl::desc("Only allow for exact function signature matches"),
    cl::init(true), cl::NotHidden);

static cl::opt<bool>
AliasSVFAnalysis("icp-alias",
    cl::desc("Use slower alias-based points-to analysis."),
    cl::init(false), cl::NotHidden);

static cl::opt<bool>
NoPromote("icp-no-promote",
    cl::desc("Don't promote indirect call, analyse only possible targets"),
    cl::init(false), cl::NotHidden);

namespace {

  class ICPPass : public ModulePass {

  public:
    static char ID;
    ICPPass() : ModulePass(ID) {}

    bool isCompatibleType(Type *T1, Type *T2) {
        // Check if 2 types are the same, tolerating void* (i8*) pointer casts.
        if (T1 == T2)
            return true;
        if (!T1->isPointerTy() || !T2->isPointerTy())
            return false;
        // If requested, be even more conservative (any pointer cast will do).
        if (TypeAnalysisOpaquePtrs)
            return true;
        return false;
    }

    bool csTypeAlias(CallSite &CS, Function *F) {
        // avoid stripping pointer casts, since we want the final called ptr type
        Value *V = CS.getCalledValue();
        FunctionType *FT= F->getFunctionType();
        FunctionType *CT= cast<FunctionType>(V->getType()->getContainedType(0));

        // Fast path: perfect type match.
        if (FT == CT)
            return true;

        // Return types have to match, unless the callsite doesn't care.
        if (!CT->getReturnType()->isVoidTy()
            && !isCompatibleType(CT->getReturnType(), FT->getReturnType()))
            return false;

        // Match #arguments and #parameters (account for variadic functions).
        if (CS.arg_size() < FT->getNumParams())
            return false;
        // Accept the case when the CallSite has more params than the function if not strict
        if (StrictSignature)
            if (CS.arg_size() > FT->getNumParams() && !F->isVarArg())
                return false;

        unsigned int max_args = StrictSignature ? CS.arg_size() : FT->getNumParams();

        // Make sure each argument has compatible type with corresponding param.
        for (unsigned i=0; i<max_args; i++) {
            Type *PT = i < FT->getNumParams() ? FT->getParamType(i) : NULL;
            if (!PT)
                break;
            if (!isCompatibleType(PT, CS.getArgument(i)->getType()))
                return false;
        }

        return true;
    }

    // Check if the signature of the CallSite is compatible with calling the function F
    bool isSignatureCompatible(CallSite &CS, Function *F) {
        // avoid stripping pointer casts, since we want the final called ptr type
        Value *V = CS.getCalledValue();
        FunctionType *FT= F->getFunctionType();
        FunctionType *CT= cast<FunctionType>(V->getType()->getContainedType(0));

        // Fast path: perfect type match.
        if (FT == CT)
            return true;

        // Return types have to match, unless the callsite doesn't care.
        if (!CT->getReturnType()->isVoidTy()
            && !isCompatibleType(CT->getReturnType(), FT->getReturnType()))
            return false;

        // Match #arguments and #parameters
        if (CS.arg_size() < FT->getNumParams())
            return false;
        
        // Accept the case when the CallSite has more params than the function
        return true;
    }

    void getIndirectCallees(Module *M, CallSite &CS, std::vector<Function*> &callees, WPAPass *wpa) {
        // Grab functions that may alias value at the callsite
        Value *V = CS.getCalledValue()->stripPointerCasts();
        for (auto &F : M->getFunctionList()) {
            if (!F.hasAddressTaken())
                continue;
            if (VarArgOnly && Fallback && !F.isVarArg())
                continue;

            if (AliasSVFAnalysis && TypeAnalysis) {
                if (csTypeAlias(CS, &F) && wpa->alias(V, &F))
                    callees.push_back(&F);
                continue;
            }

            // Use points-to analysis if requested
            if (!TypeAnalysis) {
                if (isSignatureCompatible(CS, &F) && wpa->alias(V, &F))
                    callees.push_back(&F);
                continue;
            }

            // Or faster callsite type-based analysis otherwise
            if (csTypeAlias(CS, &F))
                callees.push_back(&F);
        }
    }

    Instruction *wrapPromoteCallWithIfThenElse(llvm::CallSite CS, llvm::Function *Callee, llvm::MDNode *BranchWeights = (llvm::MDNode *)nullptr) {
        FunctionType *FT= Callee->getFunctionType();
        Instruction * newI = promoteCallWithIfThenElse(CS, Callee);
        assert(newI);
        CallBase *newCI = dyn_cast<CallBase>(newI);
        assert(newCI);

        // If the new function accepts less arguments than the callsite trim them
        if (newCI->arg_size() > FT->getNumParams()) {
            std::vector<Value*> args;
            for (auto &arg: newCI->args()) {
                if (args.size() >= FT->getNumParams()) break;
                args.push_back(arg);
            }
            CallInst *fixedCI = CallInst::Create(newCI->getCalledValue()->stripPointerCasts(), args, "", newCI);
            fixedCI->setDebugLoc(newCI->getDebugLoc());
            newCI->replaceAllUsesWith(fixedCI);
            newCI->eraseFromParent();
            return fixedCI;
        }

        return newI;
    }

    void promoteIndirectCall(Function *F, Instruction *I, WPAPass *wpa) {
        Module* M = F->getParent();
        LLVMContext& C = M->getContext();

        // retrieve the errx function
        std::vector<Type *> args;
        args.push_back(Type::getInt32Ty(C));
        args.push_back(Type::getInt8PtrTy(C));
        FunctionType *FT = FunctionType::get(Type::getVoidTy(C), args, true);
        FunctionCallee _errx = M->getOrInsertFunction("errx", FT);
        assert(_errx);
        Function *ErrxF = dyn_cast<Function>(_errx.getCallee());
        assert(ErrxF);

        oprint("Promoting indirect call: " << *I << " in " << F->getName().str());
        // Get indirect callees
        CallSite CS(I);
        std::vector<Function*> callees;
        getIndirectCallees(F->getParent(), CS, callees, wpa);
        if (callees.empty()) {
            // For now we fail if we are not using the type analysis, since we may
            // are using SVF wrongly:
            // https://github.com/SVF-tools/SVF/issues/280
            if (Abort) {
                // insert an abort call in place of the indirect default call
                Instruction *OldCall = CS.getInstruction();
                BasicBlock* ThisBB = CS.getInstruction()->getParent();

                // replace the return value of the call with undefined
                OldCall->replaceAllUsesWith(UndefValue::get(OldCall->getType()));

                // add the call to the errx function
                std::vector<Value*> args;
                args.push_back( ConstantInt::get(Type::getInt32Ty(C), 0));
                std::string str = "ICP UNREACHABLE";
                llvm::IRBuilder<> builder(ThisBB);
                static Value* error_string = builder.CreateGlobalStringPtr(StringRef(str));
                args.push_back(error_string);
                CallInst *CI = CallInst::Create(ErrxF, args, "",OldCall);
                CI->addAttribute(AttributeList::FunctionIndex, Attribute::NoReturn);

                // remove the old call and the branch to leave unreachable instr
                OldCall->eraseFromParent();
            }
            oprint("No callees available");
            return;
        }
        oprint(callees.size() << " callees possible");
        for (auto Callee : callees) {
            oprint("possible callee: " << Callee->getName().str());
        }
        if (NoPromote) return;

        // Check if we should only promote indirect calls to variadic functions.
        if (VarArgOnly) {
            bool hasVarArgCallee = false;
            for (auto Callee : callees) {
                if (Callee->isVarArg())
                    hasVarArgCallee = true;
            }
            if (!hasVarArgCallee)
                return;
        }

        // Promote with or without indirect call fallback.
        Function *lastCallee = NULL;
        for (auto Callee : callees) {
            if (lastCallee)
                wrapPromoteCallWithIfThenElse(CS, lastCallee);
            lastCallee = Callee;
        }
        if (Fallback) {
            wrapPromoteCallWithIfThenElse(CS, lastCallee);
            CS.addAttribute(AttributeList::FunctionIndex, Attribute::NoRecurse);
        }
        else if (Abort) {
            // create the last branch with the remaining indirect call
            wrapPromoteCallWithIfThenElse(CS, lastCallee);

            // insert an abort call in place of the indirect default call
            Instruction *OldCall = CS.getInstruction();
            BasicBlock* ThisBB = CS.getInstruction()->getParent();
            Instruction* LastI = ThisBB->getTerminator();
            UnreachableInst* UI = new UnreachableInst(C, LastI);

            // remove the values coming from the phi nodes of the successors
            for (BasicBlock* SuccBB: successors(ThisBB)) {
                for (PHINode &Phi: SuccBB->phis()) {
                    Phi.removeIncomingValue(ThisBB);
                }
            }

            // replace the return value of the call with undefined
            OldCall->replaceAllUsesWith(UndefValue::get(OldCall->getType()));

            // add the call to the errx function
            std::vector<Value*> args;
            args.push_back( ConstantInt::get(Type::getInt32Ty(C), 0));
            std::string str = "ICP UNREACHABLE";
            llvm::IRBuilder<> builder(ThisBB);
            static Value* error_string = builder.CreateGlobalStringPtr(StringRef(str));
            args.push_back(error_string);
            CallInst *CI = CallInst::Create(ErrxF, args, "",OldCall);
            CI->addAttribute(AttributeList::FunctionIndex, Attribute::NoReturn);

            // remove the old call and the branch to leave unreachable instr
            OldCall->eraseFromParent();
            LastI->eraseFromParent();
            assert(ThisBB->getTerminator() == UI);
        } else {
            promoteCall(CS, lastCallee);
        }
    }

    std::string getLocation(Instruction &I) {

        if (DILocation *Loc = I.getDebugLoc()) {
            unsigned Line = Loc->getLine();
            unsigned Col  = Loc->getColumn();
            StringRef File = Loc->getFilename();
            DILocation *InlineLoc = Loc->getInlinedAt();
            DILocalScope *Scope = Loc->getScope();
            // not worth
            if (Line == 0 && Col == 0 && !InlineLoc) {print(*Scope); assert(false); return "";}
            if (!InlineLoc)
                return "file: " + File.str() + ", line: " + std::to_string(Line) + ", col:" + std::to_string(Col);
            else {
                unsigned InLine = InlineLoc->getLine();
                unsigned InCol  = InlineLoc->getColumn();
                StringRef InFile = InlineLoc->getFilename();
                return "file: " + File.str() + ", line: " + std::to_string(Line) + ", col:" + std::to_string(Col) +
                    ", inlined at: " + InFile.str() + ", line: " + std::to_string(InLine) + ", col:" + std::to_string(InCol);
            }
        } else {
            assert(false);
            // No location metadata available
            return "";
        }
    }

    void dumpICFG(Function *F, WPAPass *wpa) {
        print("- function: " <<  F->getName());
        print(F->getSection());
        print(F->getSectionPrefix());
        for (BasicBlock &BB: *F) {
            for (Instruction &I : BB) {
                // Gather all call bases
                if (CallBase * CB = dyn_cast<CallBase>(&I)) {

                    // Only if they represent indirect calls to functions
                    if (CB->isInlineAsm()) continue;
                    Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                    if (Called) continue;
                    
                    CallSite CS(&I);
                    std::vector<Function*> callees;
                    getIndirectCallees(F->getParent(), CS, callees, wpa);
                    print("    - " << I);
                    print("    - " << getLocation(I));
                    for(Function *callee: callees) {
                        print("        - " << callee->getName());
                    }
                }
            }
        }
    }

    void icp(Function *F, WPAPass *wpa) {
        std::vector<Instruction *> indirectCalls;
        // dumpICFG(F, wpa);

        // Collect indirect calls.
        for (auto &BB : *F)
        for (auto &I : BB) {
            CallSite CS(&I);
            if (!CS.getInstruction() || CS.isInlineAsm())
                continue;
            if (isa<Function>(CS.getCalledValue()->stripPointerCasts()))
                continue;
            indirectCalls.push_back(&I);
        }

        // Promote.
        for (auto I : indirectCalls) {
            promoteIndirectCall(F, I, wpa);
        }
    }

    virtual bool runOnModule(Module &M) {
        icpPassLog("Running...");
        assert(!(Abort && Fallback) && 
            "Only a mode between icp-unreachable and icp-fallback can be selected");
        SVFModule* svfModule = LLVMModuleSet::getLLVMModuleSet()->buildSVFModule(M);
        WPAPass *wpa = NULL;
        assert(AliasSVFAnalysis || TypeAnalysis);
        if (AliasSVFAnalysis) {
            wpa = new WPAPass();
            wpa->runOnModule(svfModule);
        }

        std::vector<Regex*> FunctionRegexes;
        if (Functions.empty())
            Functions.push_back(".*");
        passListRegexInit(FunctionRegexes, Functions);

        // ICP all the functions in the module.
        for (auto &F : M.getFunctionList()) {
            if (F.isDeclaration())
                continue;
            const std::string &FName = F.getName();
            if (!passListRegexMatch(FunctionRegexes, FName))
                continue;
            icp(&F, wpa);
        }

        return true;
    }
  };

}

char ICPPass::ID = 0;
RegisterPass<ICPPass> MP("icp", "ICP Pass");
