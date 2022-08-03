//===- LoopDeletion.cpp - Dead Loop Deletion Pass ---------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//
//
// This file implements the Dead Loop Deletion Pass. This pass is responsible
// for eliminating loops with non-infinite computable trip counts that have no
// side effects or volatile instructions, and do not contribute to the
// computation of the function's return value.
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Scalar/LoopDeletion.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/GlobalsModRef.h"
#include "llvm/Analysis/LoopPass.h"
#include "llvm/Analysis/MemorySSA.h"
#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/PatternMatch.h"
#include "llvm/InitializePasses.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/LoopUtils.h"

using namespace llvm;

namespace {
class BoundsCheckPass : public FunctionPass {
public:
  static char ID; // Pass ID, replacement for typeid
  BoundsCheckPass() : FunctionPass(ID) {
     initializeBoundsCheckPassPass(*PassRegistry::getPassRegistry());
  }

  // Possibly eliminate loop L if it is dead.
  bool runOnFunction(Function &F) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addPreserved<MemorySSAWrapperPass>();
  }
};
}

char BoundsCheckPass::ID = 0;
INITIALIZE_PASS_BEGIN(BoundsCheckPass, "loop-deletion",
                      "Delete dead loops", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopPass)
INITIALIZE_PASS_END(BoundsCheckPass, "loop-deletion",
                    "Delete dead loops", false, false)

Pass *llvm::createBoundsCheck() { return new BoundsCheckPass(); }

bool BoundsCheckPass::runOnFunction(Function &F) {
  return false;
}