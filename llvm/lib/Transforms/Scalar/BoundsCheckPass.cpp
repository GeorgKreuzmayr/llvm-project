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
class BoundsCheckPass : public FunctionPass {
public:
  static char ID; // Pass ID, replacement for typeid
  BoundsCheckPass() : FunctionPass(ID) {
     initializeBoundsCheckPassPass(*PassRegistry::getPassRegistry());
  }

  bool runOnFunction(Function &F) override {
    /*
    if(!F.getName().equals("wasmer_function__5")){
      return false;
    }

    for(auto&BasicBlock : F){
      for(auto&Instruction : BasicBlock){
        // Instruction.dump();
        if(Instruction.getMetadata(10) != nullptr){
          if(auto*StringMetaData = dyn_cast<MDString>(
                  Instruction.getMetadata(10)->getOperand(0).get())) {
            if (StringMetaData->getString().equals("wasmer_bounds_check")) {
              // Found memory access with bounds check

              // assume vec + i less than 2000
              if(Instruction.getOperand(0)->hasName()){
                if(Instruction.getOperand(0)->getName().equals("ptr_in_bounds_expect")){
                  auto* CmpInstruction = dyn_cast<ICmpInst>(Instruction.getPrevNode()->getPrevNode());
                  auto* VecAndI = dyn_cast<AddOperator>(CmpInstruction->getOperand(0));
                  ICmpInst *VecAndICmp = new ICmpInst(ICmpInst::ICMP_ULT, VecAndI, ConstantInt::get(VecAndI->getType(), 2000, false));
                  VecAndICmp->insertBefore(CmpInstruction);
                  assumeCMPIsTrue(VecAndICmp);
                }
              }

              // assume ptr_in_bounds_expect == true

              auto *Prev = Instruction.getPrevNode();
              while (!dyn_cast<ICmpInst>(Prev)) {
                Prev = Prev->getPrevNode();
              }
              // Cmp Instruction for bounds check
              auto *ICMPInst = dyn_cast<ICmpInst>(Prev);
              assumeCMPIsTrue(ICMPInst);

            }
          }
        }
      }
    }
    return true;
     */
    return false;
  }
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<AssumptionCacheTracker>();
    AU.addPreserved<AssumptionCacheTracker>();
    // AU.addRequired<LoopInfo>();
  }

private:
  void assumeCMPIsTrue(ICmpInst* ICMPInst){
    Function *AssumeIntrinsic = Intrinsic::getDeclaration(
        ICMPInst->getModule(), Intrinsic::assume);
    CallInst *CI = CallInst::Create(AssumeIntrinsic, {ICMPInst});
    CI->insertAfter(ICMPInst);
    AssumptionCache AC = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(*ICMPInst->getFunction());
    AC.registerAssumption(CI);
  }
};
}

char BoundsCheckPass::ID = 0;
INITIALIZE_PASS_BEGIN(BoundsCheckPass, "bounds-check",
                      "Delete dead loops", false, false)
INITIALIZE_PASS_DEPENDENCY(LoopPass)
INITIALIZE_PASS_DEPENDENCY(AssumptionCacheTracker)
INITIALIZE_PASS_END(BoundsCheckPass, "bounds-check",
                    "Delete dead loops", false, false)

Pass *llvm::createBoundsCheck() { return new BoundsCheckPass(); }