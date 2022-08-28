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

#include "llvm/Analysis/LoopPass.h"
#include "llvm/IR/Dominators.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Scalar/LoopPassManager.h"
#include "llvm/Transforms/Utils/LoopUtils.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/ValueMapper.h"


#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/ScalarEvolution.h"



using namespace llvm;

namespace {
class WasmerLoopPass : public LoopPass {
public:
  static char ID; // Pass ID, replacement for typeid
  WasmerLoopPass() : LoopPass(ID) {
  }

  bool runOnLoop(Loop *L, LPPassManager &LPM) override {
    if(!L->getLoopPreheader()->getParent()->getName().equals("wasmer_function__5")){
      return false;
    }

    ValueToValueMapTy  VMap;
    auto* LastPreLoopBlock = L->getLoopPreheader();
    for(auto* BB : L->getBlocks()){
      auto* LastInstruction = &BB->getInstList().back();
      if(isAnnotated(LastInstruction)){
        // Last instruction is annotated branch after bounds check
        auto* Branch = dyn_cast<BranchInst>(LastInstruction);
        assert(Branch);
        // TODO: Update PHI Nodes?
        auto* BBDash = CloneBasicBlock(BB, VMap, "_bounds_check", BB->getParent());
        VMap[BB] = BBDash;
        for(auto& Inst : *BBDash){
          RemapInstruction(&Inst, VMap, RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
        }
        assumeIndexIsInBounds(BB);
        auto LB = getLoopBounds(L);
        replaceIndexWithMax(BBDash, LB.IndexPointer, LB.MaxValue);
        addBBDashToPreHeader(LastPreLoopBlock, BBDash, L);
        LastPreLoopBlock = BBDash;
      }
    }
    return true;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<ScalarEvolutionWrapperPass>();
    AU.addRequired<AssumptionCacheTracker>();
    AU.addPreserved<AssumptionCacheTracker>();
    getLoopAnalysisUsage(AU);
  }

private:
  struct LoopBounds {
    Value* IndexPointer;
    int MaxValue;
  };

  LoopBounds getLoopBounds(Loop * L){
    auto* BB = L->getHeader();
    auto it = BB->begin();
    ++it;
    ++it;
    auto& inst = *it;
    auto* load = dyn_cast<LoadInst>(&inst);
    auto* local1 = load->getOperand(0);
    return {local1, 200000000};
  }

  bool isAnnotated(Instruction* Inst){
    if (Inst->getMetadata(10) != nullptr) {
      if (auto *StringMetaData =
              dyn_cast<MDString>(Inst->getMetadata(10)->getOperand(0).get())) {
        if (StringMetaData->getString().equals("wasmer_bounds_check")) {
          return true;
        }
      }
    }
    return false;
  }

  void addBBDashToPreHeader(BasicBlock *LastPreLoopBlock, BasicBlock *BBDash, Loop* L){
    auto* PreHeaderBranch = dyn_cast<BranchInst>(&LastPreLoopBlock->getInstList().back());
    assert(PreHeaderBranch);
    PreHeaderBranch->setSuccessor(0, BBDash);
    auto* BBDashBranch = dyn_cast<BranchInst>(&BBDash->getInstList().back());
    assert(BBDashBranch);
    BBDashBranch->setSuccessor(0, L->getHeader());
  }

  void replaceIndexWithMax(BasicBlock *BB, Value*IndexPointer, int MaxValue) {
    for(auto&Instruction : *BB){
      for(uint64_t I = 0; I < Instruction.getNumOperands(); ++I){
        auto*Operand = Instruction.getOperand(I);
        if(Operand == IndexPointer){
          // Found Load of Index
          auto* Load = dyn_cast<LoadInst>(&Instruction);
          assert(Load);
          auto* MaxConst = ConstantInt::get(Load->getType(), MaxValue, false);
          // Replace index with its maximum value
          Instruction.replaceAllUsesWith(MaxConst);
        }
      }
    }
  }

  void assumeIndexIsInBounds(BasicBlock *BB){
    auto* LastInst = &BB->getInstList().back();
    assert(isAnnotated(LastInst));
    auto *Prev = LastInst->getPrevNode();
    while (!dyn_cast<ICmpInst>(Prev)) {
      Prev = Prev->getPrevNode();
    }
    // Cmp Instruction for bounds check
    auto *ICMPInst = dyn_cast<ICmpInst>(Prev);
    Function *AssumeIntrinsic = Intrinsic::getDeclaration(
        ICMPInst->getModule(), Intrinsic::assume);
    CallInst *CI = CallInst::Create(AssumeIntrinsic, {ICMPInst});
    CI->insertAfter(ICMPInst);
    AssumptionCache AC = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(*ICMPInst->getFunction());
    AC.registerAssumption(CI);
  }
};
}

char WasmerLoopPass::ID = 0;
static RegisterPass<WasmerLoopPass> X("wasmer-loop", "Hello World Pass",
                                          false /* Only looks at CFG */,
                                          false /* Analysis Pass */);


static RegisterStandardPasses Y(
    PassManagerBuilder::EP_EarlyAsPossible,
    [](const PassManagerBuilder &Builder,
       legacy::PassManagerBase &PM) { PM.add(new WasmerLoopPass()); });

Pass *llvm::createBoundsCheckLoop() { return new WasmerLoopPass(); }