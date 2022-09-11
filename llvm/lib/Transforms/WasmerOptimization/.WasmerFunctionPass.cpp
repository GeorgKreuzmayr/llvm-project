#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/WasmerPass.h"
#include <iostream>

namespace llvm {
struct WasmerFunctionPass : public FunctionPass {
  static char ID;
  WasmerFunctionPass() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    auto &Ctx = F.getContext();

    // Find Start of Memory and Max Memory Pointer in entry block
    for (auto &Instruction : F.getEntryBlock()) {
      if (auto *GEP = dyn_cast<GetElementPtrInst>(&Instruction)) {
        if (GEP->getNumOperands() == 2) {
          // First argument is start of metadata
          if (GEP->getOperand(0) == F.getArg(0)) {
            // Second argument is offset by 180 or 188
            // TODO: Check why it differs
            if (GEP->getOperand(1) ==
                    ConstantInt::get(IntegerType::getInt32Ty(Ctx), 180) ||
                GEP->getOperand(1) ==
                    ConstantInt::get(IntegerType::getInt32Ty(Ctx), 188)) {

              // Bitcast to {i8*, i64}*
              if (auto *BitCast = dyn_cast<BitCastInst>(GEP->getNextNode())) {

                // Retrieve Memory Start
                if (auto *GEPMemStart =
                        dyn_cast<GEPOperator>(BitCast->getNextNode())) {
                  if (GEPMemStart->getType() ==
                      PointerType::get(PointerType::getInt8PtrTy(Ctx), 0)) {
                    auto *MemoryStart =
                        dyn_cast<llvm::Instruction>(GEPMemStart);
                    MemoryStart->addAnnotationMetadata(MemoryStartValue);
                  }
                }

                // Retrieve Max Memory
                if (auto *GEPMaxMem = dyn_cast<GEPOperator>(
                        BitCast->getNextNode()->getNextNode())) {
                  if (GEPMaxMem->getType() == PointerType::getInt64PtrTy(Ctx)) {
                    auto *MaxMemory = dyn_cast<llvm::Instruction>(GEPMaxMem);
                    MaxMemory->addAnnotationMetadata(MaxMemoryAnno);
                  }
                }
              }
            }
          }
        }
      }
    }

    // Annotate Instructions
    for (auto &BasicBlock : F) {
      for (auto &Instruction : BasicBlock) {
        // Annotate load of max memory and memory start
        if (auto *Load = dyn_cast<LoadInst>(&Instruction)) {
          if (auto *GEP = dyn_cast<llvm::Instruction>(Load->getOperand(0))) {
            if (isAnnotated(GEP, MaxMemoryAnno)) {
              Load->addAnnotationMetadata(MaxMemoryLoadAnno);
            } else if (isAnnotated(GEP, MemoryStartValue)) {
              Load->addAnnotationMetadata(LoadMemoryStart);
            }
          }
        }

        // Annotate heap accessing GEP instructions and used index
        if (auto *GEP = dyn_cast<GEPOperator>(&Instruction)) {
          if (GEP->getNumOperands() == 2) {
            if (auto *FirstOp =
                    dyn_cast<llvm::Instruction>(GEP->getOperand(0))) {
              if (isAnnotated(FirstOp, LoadMemoryStart)) {
                Instruction.addAnnotationMetadata(AccessHeapMemory);
              }
              if (auto *SecondOp =
                      dyn_cast<llvm::Instruction>(GEP->getOperand(1))) {
                SecondOp->addAnnotationMetadata(MemoryAccessIndex);
              }
            }
          }
        }

        // Annotate store to local variables
        if (auto *Store = dyn_cast<StoreInst>(&Instruction)) {
          if (auto *StoreDest =
                  dyn_cast<llvm::Instruction>(Store->getOperand(1))) {
            if (isAnnotated(StoreDest, MaxMemoryAnno)) {
              // Annotate that function should not be optimized, if store to max
              // memory location
              annotateFunction(F);
              assert(false); // TODO: Check if every triggered
            } else if (auto *Alloca = dyn_cast<AllocaInst>(StoreDest)) {
              // Annotate the if a local variable is written only once or
              // multiple times in this function
              // TODO: Check if we actually need this
              if (!isAnnotated(Alloca, InitialStoreAnno)) {
                Alloca->addAnnotationMetadata(InitialStoreAnno);
              } else if (!isAnnotated(Alloca, StoreAnno)) {
                Alloca->addAnnotationMetadata(StoreAnno);
              }
            }
          }
        }
      }
    }

    return false;
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AssumptionCacheTracker>();
    AU.addPreserved<AssumptionCacheTracker>();
  }
};
} // namespace llvm

char llvm::WasmerFunctionPass::ID = 0;
static llvm::RegisterPass<llvm::WasmerFunctionPass>
    X("wasmer-function", "Hello World Pass", false /* Only looks at CFG */,
      true /* Analysis Pass */);

static llvm::RegisterStandardPasses
    Y(llvm::PassManagerBuilder::EP_EarlyAsPossible,
      [](const llvm::PassManagerBuilder &Builder,
         llvm::legacy::PassManagerBase &PM) {
        PM.add(new llvm::WasmerFunctionPass());
      });