
#include <pass.h>
#include <cgc_magics.h>
#include "llvm/Analysis/CFG.h"

using namespace llvm;

#define DEBUG_TYPE "FuncStats"
#define FuncStatsPassLog(M) LLVM_DEBUG(dbgs() << "FuncStatsPass: " << M << "\n")
#define oprint(s) outs() << s << "\n"

static cl::opt<bool>
DumpCalls("dump-calls",
    cl::desc("Dump all non unique calls"),
    cl::init(false), cl::NotHidden);

static cl::opt<bool>
DumpGraph("dump-graph",
    cl::desc("Dump the Call Graph"),
    cl::init(false), cl::NotHidden);

static cl::opt<bool>
DumpWeights("dump-weights",
    cl::desc("Dump the CGC weights"),
    cl::init(false), cl::NotHidden);

static cl::opt<std::string>
RootFunction("dump-weights-root",
    cl::desc("Specify the root functions where to start dumping weights"),
    cl::init(""), cl::NotHidden);

namespace {

  class FuncStatsPass : public ModulePass {

  public:
    static char ID;
    FuncStatsPass() : ModulePass(ID) {}

    // Return true if `F` has an available_externally linkage (i.e. equivalent to a declaration)
    bool isAvailableExternally(Function &F) {
        GlobalValue::LinkageTypes L = F.getLinkage();
        return GlobalValue::isAvailableExternallyLinkage(L);
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

    void dumpWeights(Function *F, int level, std::set<Function*> &visited) {
      if (visited.find(F) != visited.end()) return;
      visited.insert(F);

      for (BasicBlock &BB: *F) {
        for (Instruction &I: BB) {
          // Search all call bases
          if (CallBase * CB = dyn_cast<CallBase>(&I)) {

            // Only if they represent direct calls to functions
            if (CB->isInlineAsm()) continue;
            Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
            if (!Called || Called->isDeclaration() || Called->isIntrinsic()) continue;

            oprint(std::string(level, '\t') << "|-> [" << getPriority(CB) << "] " << Called->getName());
            dumpWeights(Called, level+1, visited);
          }
        }
      }
    }

    virtual bool runOnModule(Module &M) override {
      unsigned int num_funcs = 0;
      unsigned int total_BB = 0;
      unsigned int total_edges = 0;
      std::map<Function*, int> callsToFunc;
      for (auto &F : M.getFunctionList()) {
        if (F.isDeclaration())
          continue;
        ++num_funcs;
        if (DumpGraph) {
          oprint("Call graph node for function: '" << F.getName() << "'");
        }
        total_edges += estimateAFLEdges(&F);
        for(auto &BB: F) {
          ++total_BB;
          if (DumpCalls || DumpGraph) {
            for (auto &I : BB) {
              if (CallBase * CB = dyn_cast<CallBase>(&I)) {
                if (CB->isInlineAsm()) continue;

                Function *Called = dyn_cast<Function>(CB->getCalledOperand()->stripPointerCasts());
                if (!Called || Called->isDeclaration() || Called->isIntrinsic() || isAvailableExternally(*Called)) continue;
                callsToFunc[Called]+=1;
                if (DumpGraph) {
                  oprint("    " << F.getName() << " calls function '" << Called->getName() << "'");
                }
              }
            }
          }
        }
      }

      oprint("Num functions: " << num_funcs);
      oprint("Num BBs      : " << total_BB);
      oprint("AFL edges    : " << total_edges);

      if (DumpCalls) {
        for (auto elem: callsToFunc) {
          Function* F = elem.first;
          int calls   = elem.second;
          if (calls > 1) oprint(F->getName().str() << ": " << calls);
        }
      }

      if (DumpWeights) {
        for (Function &F: M) {
            if (F.isDeclaration())
              continue;

            // start from root
            const std::string &FName = F.getName().str();
            std::set<Function*> visited;
            if (FName == RootFunction) {
              oprint(F.getName());
              dumpWeights(&F, 0, visited);
            }
        }
      }

      return false;
    }

    void getAnalysisUsage(AnalysisUsage &AU) const override {
        AU.addRequired<DominatorTreeWrapperPass>();
        AU.addRequired<PostDominatorTreeWrapperPass>();
    }
  };

}

char FuncStatsPass::ID = 0;
RegisterPass<FuncStatsPass> MP("func-stats", "FuncStats Pass");

