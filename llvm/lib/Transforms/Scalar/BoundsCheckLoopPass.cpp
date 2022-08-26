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
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Analysis/AssumptionCache.h"

using namespace llvm;

namespace {
class BoundsCheckLoopPass : public LoopPass {
public:
  static char ID; // Pass ID, replacement for typeid
  BoundsCheckLoopPass() : LoopPass(ID) {
    initializeBoundsCheckLoopPassPass(*PassRegistry::getPassRegistry());
  }

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    L->dump();
    return true;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AssumptionCacheTracker>();
    AU.addPreserved<AssumptionCacheTracker>();
  }

};
}

char BoundsCheckLoopPass::ID = 0;
INITIALIZE_PASS_BEGIN(BoundsCheckLoopPass, "bounds-check-loop",
                      "Delete dead loops", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopPass)
INITIALIZE_PASS_DEPENDENCY(AssumptionCacheTracker)
INITIALIZE_PASS_END(BoundsCheckLoopPass, "bounds-check-loop",
                    "Delete dead loops", false, false)

Pass *llvm::createBoundsCheckLoop() { return new BoundsCheckLoopPass(); }