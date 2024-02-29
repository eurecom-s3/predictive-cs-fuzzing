
#include <pass.h>
#include <iostream>
#include <fstream>
#include <unistd.h>

using namespace llvm;

#define DEBUG_TYPE "DumpCallTree"
#define DumpCallTreePassLog(M) LLVM_DEBUG(dbgs() << "DumpCallTreePass: " << M << "\n")
#define oprint(s) outs() << s << "\n"

static cl::opt<std::string>
CallTreeStart("call-tree-start",
    cl::desc("Specify the function from where to start the visit of the call tree to dump"),
    cl::ZeroOrMore, cl::CommaSeparated, cl::NotHidden);

static cl::opt<std::string>
OutFilename("dump-tree-file",
    cl::desc("The file where to dump the called tree"),
    cl::init("call-tree.log"), cl::NotHidden);

namespace {

  // Dump the subtree of the CFG functions starting from `call-tree-start`
  class DumpCallTreePass : public ModulePass {

  std::set<std::string> CalledSet;
  std::set<Function*> ToVisit;

  public:
    static char ID;
    DumpCallTreePass() : ModulePass(ID) {}

    void visit(Function* F) {
      CalledSet.insert(F->getName().str());
      // For each call in the given function:
      for (auto &BB : *F)
      for (auto &I : BB) {
        if (CallBase * CB = dyn_cast<CallBase>(&I)) {
          if (CB->isInlineAsm()) continue;

          Function *C = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
          if (C) {
            if (C->isDeclaration() || C->isIntrinsic())
              continue;
            
            // If never saw the function add to the visit
            if (CalledSet.find(C->getName().str()) == CalledSet.end())
              ToVisit.insert(C);
          }
        }
      }
    }

    virtual bool runOnModule(Module &M) {
      for (auto &F : M.getFunctionList()) {
        if (F.isDeclaration())
          continue;
        if (!F.getName().equals(CallTreeStart))
          continue;
        ToVisit.insert(&F);
        break;
      }

      // Start from root function and iteratively visit the callgraph.
      while (!ToVisit.empty()) {
          Function *F = *ToVisit.begin();
          ToVisit.erase(ToVisit.begin());
          visit(F);
      }

      std::ofstream ofile;
      ofile.open(OutFilename, std::ios::out | std::ios::trunc);
      assert(ofile.is_open());

      for (auto s: CalledSet) {
        ofile << s << std::endl;
      }
      ofile.flush();
      ofile.close();

      return false;
    }
  };

}

char DumpCallTreePass::ID = 0;
RegisterPass<DumpCallTreePass> MP("dump-call-tree", "DumpCallTree Pass");

