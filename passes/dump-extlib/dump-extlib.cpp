
#include <pass.h>
#include <iostream>
#include <fstream>

using namespace llvm;

#define DEBUG_TYPE "DumpExtlib"
#define DumpExtlibPassLog(M) LLVM_DEBUG(dbgs() << "DumpExtlibPass: " << M << "\n")
#define oprint(s) (outs() << s << "\n")

static cl::list<std::string>
Whitelist("dumpext-whitelist",
    cl::desc("Specify the comma-separated path regexes for the whitelist"),
    cl::OneOrMore, cl::CommaSeparated, cl::NotHidden);

static cl::list<std::string>
Blacklist("dumpext-blacklist",
    cl::desc("Specify the comma-separated path regexes for the blacklist"),
    cl::OneOrMore, cl::CommaSeparated, cl::NotHidden);

static cl::opt<std::string>
OutFilename("dumpext-out",
    cl::desc("Specify the name of the file where the function list will be saved [- for stdout]"),
    cl::init("-"), cl::NotHidden);

static cl::opt<bool>
Dbg("dumpext-dbg", cl::desc("Debug Mode"),
    cl::init(false));

namespace {
  // This pass tries to find in the module all the function that are identified
  // being part of linked static libraries.
  // It uses a really simple euristic where it takes a whitelist and assumes
  // a function being a library one if the DebugInfo of that function points to 
  // a path not containing any token in the whitelist.
  //
  // e.g. whitelist: curl
  // path: /src/curl/lib/    -> ok
  // path: /src/nghttp2/lib/ -> lib function
  //
  // The pass writes a function list to be passed to llvm-extract
  class DumpExtlibPass : public ModulePass {

  public:
    static char ID;
    DumpExtlibPass() : ModulePass(ID) {}

    std::string dirnameOf(const std::string& fname)
    {
        size_t pos = fname.find_last_of("/");
        return (std::string::npos == pos)
            ? fname
            : fname.substr(0, pos);
    }

    std::string getFileDirectory(Function &F) {
        if (DISubprogram *Loc = F.getSubprogram()) {
            // The path from the CWD to the source file, while building
            StringRef File = Loc->getFilename();
            // CWD while building
            StringRef Directory = Loc->getDirectory();

            std::string Path = Directory.str() + "/" + File.str();
            return dirnameOf(Path);
        } else {
            // oprint(F.getName());
            // assert(false);
            // No location metadata available
            return "";
        }
    }

    std::string getCompilationDirectory(Function &F) {
        if (DISubprogram *Loc = F.getSubprogram()) {
            // The path from the CWD to the source file, while building
            // StringRef File = Loc->getFilename();
            // CWD while building
            StringRef Directory = Loc->getDirectory();
            return Directory.str();
        } else {
            // oprint(F.getName());
            // assert(false);
            // No location metadata available
            return "";
        }
    }

    virtual bool runOnModule(Module &M) {

        // Initialize regular expressions for whitelist
        std::vector<Regex*> WhitelistRegexes;
        assert (!Whitelist.empty());
        passListRegexInit(WhitelistRegexes, Whitelist);

        // Initialize regular expressions for blacklist
        std::vector<Regex*> BlacklistRegexes;
        if (Blacklist.empty()) {
            Blacklist.push_back("EMPTY_BLACKLIST_SHOULD_NOT_MATCH_ANYTHING");
        }
        passListRegexInit(BlacklistRegexes, Blacklist);

        std::vector<Function*> ToExtract;
        std::map<Function*, int> callsToFunc;

        // first remove all the aliases, since once we extract the functions we may invalidate some
        std::set<GlobalAlias*> aliasesToRemove;
        for (GlobalAlias &A: M.getAliasList()) {
            A.replaceAllUsesWith(A.getAliasee());
            aliasesToRemove.insert(&A);
        }
        for (GlobalAlias *A: aliasesToRemove) A->eraseFromParent();
        
        for (auto &F : M.getFunctionList()) {
            if (F.isDeclaration())
                continue;

            const std::string &DirName = getFileDirectory(F);
            const std::string &CompilationDir = getCompilationDirectory(F);

            // if the function does not have any debug info stay safe and assume
            // that it belongs to the original program
            if (DirName == "") continue;

            // If either the directory of the source file of the function or 
            // the compilation directory matches the whitelist then keep the function
            if (passListRegexMatch(WhitelistRegexes, DirName) || passListRegexMatch(WhitelistRegexes, CompilationDir)) {
                if (Dbg) {
                    oprint("Keep " << F.getName().str() << ": " << DirName);
                }

                // only if the blacklist does not match then skip extraction and leave it in the bitcode
                if (!passListRegexMatch(BlacklistRegexes, DirName) && !passListRegexMatch(BlacklistRegexes, CompilationDir)) {
                    // continue and skip the extraction
                    continue;
                }
            }

            ToExtract.push_back(&F);
            if (Dbg) {
                oprint("Remove " << F.getName().str() << ": " << DirName);
            }
        }

        std::string result = "";
        for (Function *F: ToExtract) {
            result.append(" -func=");
            // result.append("^");
            result.append(F->getName().str());
            // result.append("$|");
        }
        // result.replace(result.rfind("|"), 1, ")");

        if (OutFilename == "-") {
            outs() << result << "\n";
        } else {
            std::ofstream ofile;
            ofile.open(OutFilename, std::ios::out | std::ios::trunc);
            assert(ofile.is_open());

            ofile << result;
            ofile.flush();
            ofile.close();
        }
        return true;
    }
  };

}

char DumpExtlibPass::ID = 0;
RegisterPass<DumpExtlibPass> MP("dump-extlib", "DumpExtlib Pass");

