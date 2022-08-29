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
#include <iostream>



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

    auto LB = getLoopBounds(L);
    if(!LB.IndexPointer || !LB.MaxValue){
      return false;
    }

    ValueToValueMapTy  VMap;
    auto* LastPreLoopBlock = L->getLoopPreheader();
    // Analysis Loop
    std::vector<AllocaInst*> Allocas;
    for(auto* BB : L->getBlocks()){
      for(auto& Instruction : *BB){

        if(auto* Alloca = dyn_cast<AllocaInst>(&Instruction)){
          Allocas.push_back(Alloca);
        }

        if(auto* Store = dyn_cast<StoreInst>(&Instruction)){
          for(auto* Alloca : Allocas){
            if(Store->getOperand(1) == Alloca){
              if(!isAnnotated(Alloca, "NotLoopIV")){
                Alloca->addAnnotationMetadata("NotLoopIV");
              }
            }
          }
        }

        if(auto* Load = dyn_cast<LoadInst>(&Instruction)){
          if(isAnnotated(Load, "MemoryStartLoad")){
            if(auto* GEP = dyn_cast<GEPOperator>(Load->getNextNode())){
              if(GEP->getOperand(0) == Load && GEP->getNumOperands() == 2){
                auto* MemAddrInstr = reinterpret_cast<llvm::Instruction*>(GEP->getOperand(1));
                if(auto* MemAddrAdd = dyn_cast<AddOperator>(MemAddrInstr)){
                  // Found Memory Access


                  // Check if previous BB ends with bounds_check annotation
                  auto* PrevBB = BB->getPrevNode();
                  if(auto* Branch = dyn_cast<BranchInst>(&PrevBB->getInstList().back())){
                    if(isAnnotated(Branch, "wasmer_bounds_check")){

                    }
                  }

                  Load->dump();
                  GEP->dump();
                  MemAddrAdd->dump();
                }
              }
            }
          }
        }
      }
    }

    for(auto* BB : L->getBlocks()){
      auto* LastInstruction = &BB->getInstList().back();
      if(isAnnotated(LastInstruction, "wasmer_bounds_check")){
        // Last instruction is annotated branch after bounds check
        auto* Branch = dyn_cast<BranchInst>(LastInstruction);
        assert(Branch);
        auto* BBDash = CloneBasicBlock(BB, VMap, "_bounds_check", BB->getParent());
        VMap[BB] = BBDash;
        for(auto& Inst : *BBDash){
          RemapInstruction(&Inst, VMap, RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
        }
        assumeIndexIsInBounds(BB);
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
    Value* MaxValue;
  };

  LoopBounds getLoopBounds(Loop * L){
    auto* BB = L->getBlocks().back();
    for(auto It = BB->rbegin(); It != BB->rend(); ++It){
      if(auto* ICmp = dyn_cast<ICmpInst>(&*It)){
        if(auto* Store = dyn_cast<StoreInst>(&(*++It))){
          if(auto* Add = dyn_cast<AddOperator>(&(*++It))) {
            if (auto *Load = dyn_cast<LoadInst>(&(*++It))) {
              if(Store->getOperand(1) == Load->getOperand(0)){
                if(ICmp->getOperand(0) == Add){
                  std::cerr << "Bounds found: ";
                  Load->dump();
                  return {Load->getOperand(0), ICmp->getOperand(1)};
                }
              }
            }
          }
        }
      }
    }
    return { nullptr, nullptr};
  }

  bool isAnnotated(Instruction* Inst, std::string_view Annotation){
    auto* MetaData = Inst->getMetadata(LLVMContext::MD_annotation);
    if(!MetaData){
      MetaData = Inst->getMetadata(10);
    }
    if (MetaData) {
      for (size_t Idx = 0; Idx < MetaData->getNumOperands(); ++Idx) {
        if (auto *StringMetaData =
                dyn_cast<MDString>(MetaData->getOperand(Idx).get())) {
          if (StringMetaData->getString().equals(Annotation.data())) {
            return true;
          }
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

  void replaceIndexWithMax(BasicBlock *BB, Value*IndexPointer, Value* MaxValue) {
    for(auto&Instruction : *BB){
      for(uint64_t I = 0; I < Instruction.getNumOperands(); ++I){
        auto*Operand = Instruction.getOperand(I);
        if(Operand == IndexPointer){
          // Found Load of Index
          auto* Load = dyn_cast<LoadInst>(&Instruction);
          assert(Load);
          // Replace index with its maximum value
          Instruction.replaceAllUsesWith(MaxValue);
        }
      }
    }
  }

  void assumeIndexIsInBounds(BasicBlock *BB){
    auto* LastInst = &BB->getInstList().back();
    assert(isAnnotated(LastInst, "wasmer_bounds_check"));
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