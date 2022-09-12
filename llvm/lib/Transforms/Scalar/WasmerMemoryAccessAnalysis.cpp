//===- WasmerMemoryAccessAnalysis.cpp - Memory Access Analysis ------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This analysis pass annotates the useful information concerning web assembly
// memory accesses, compiled by wasmer. Those are used in the
// WasmerBoundsCheckLoopOptimization.cpp
//
//===----------------------------------------------------------------------===//

#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Transforms/WasmerPass.h"

using namespace llvm;

namespace {
class WasmerMemoryAccessAnalysis : public FunctionPass {
public:
  static char ID;
  WasmerMemoryAccessAnalysis() : FunctionPass(ID) {
    initializeWasmerMemoryAccessAnalysisPass(*PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &F) override {
    auto &Ctx = F.getContext();

    // Find Start of Memory and Max Memory Pointer in entry block
    for (auto &Instruction : F.getEntryBlock()) {
      if (auto *GEP = dyn_cast<GetElementPtrInst>(&Instruction)) {
        if (GEP->getNumOperands() == 2) {
          // First argument is start of metadata
          if (GEP->getOperand(0) == F.getArg(0)) {
            // Bitcast to {i8*, i64}*
            if (auto *BitCast = dyn_cast<BitCastInst>(GEP->getNextNode())) {
              // Annotate Memory Start
              if (auto *GEPMemStart =
                      dyn_cast<GEPOperator>(BitCast->getNextNode())) {
                if (GEPMemStart->getType() ==
                        PointerType::get(PointerType::getInt8PtrTy(Ctx), 0) &&
                    GEPMemStart->getOperand(0) == BitCast) {
                  auto *MemoryStart = dyn_cast<llvm::Instruction>(GEPMemStart);
                  MemoryStart->addAnnotationMetadata(MemoryStartValue);
                }

                // Annotate Max Memory
                if (auto *GEPMaxMem = dyn_cast<GEPOperator>(
                        BitCast->getNextNode()->getNextNode())) {
                  if (GEPMaxMem->getType() == PointerType::getInt64PtrTy(Ctx) &&
                      GEPMaxMem->getOperand(0) == BitCast) {
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
              assert(false); // TODO: Check if ever triggered
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
};
} // namespace

char WasmerMemoryAccessAnalysis::ID = 0;
INITIALIZE_PASS(WasmerMemoryAccessAnalysis, "bounds-check",
                "Interval Partition Construction", false, true)

Pass *llvm::createWasmerMemoryAccessAnalysis() {
  return new WasmerMemoryAccessAnalysis();
}