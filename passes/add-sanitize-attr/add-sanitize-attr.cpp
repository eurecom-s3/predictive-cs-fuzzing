
#include <pass.h>

using namespace llvm;

#define DEBUG_TYPE "AddSanitizeAttr"
#define AddSanitizeAttrPassLog(M) LLVM_DEBUG(dbgs() << "AddSanitizeAttrPass: " << M << "\n")
#define oprint(s) outs() << s << "\n"

namespace {

  class AddSanitizeAttrPass : public ModulePass {

  public:
    static char ID;
    AddSanitizeAttrPass() : ModulePass(ID) {}

    virtual bool runOnModule(Module &M) {
        for (auto &F : M.getFunctionList()) {
            if (F.isDeclaration())
                continue;

            // if(!F.hasFnAttribute(Attribute::NoSanitize))
            F.addFnAttr(Attribute::SanitizeAddress);
        }

      return true;
    }
  };

}

char AddSanitizeAttrPass::ID = 0;
RegisterPass<AddSanitizeAttrPass> MP("add-sanitize-attr", "AddSanitizeAttr Pass");

