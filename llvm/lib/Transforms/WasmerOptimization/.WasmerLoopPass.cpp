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
#include <unordered_map>



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


    // Annotate Loop
    for(auto* BB : L->getBlocks()){
      for(auto& Instruction : *BB){

        // Annotate that Alloca as NotLoopIV, if stored to
        if(auto* Store = dyn_cast<StoreInst>(&Instruction)){
          auto* StoreDest = reinterpret_cast<llvm::Instruction*>(Store->getOperand(1));
          if(auto* Alloca = dyn_cast<AllocaInst>(StoreDest)){
            if(Store->getOperand(1) == Alloca){
              if(!isAnnotated(Alloca, "NotLoopIV")){
                Alloca->addAnnotationMetadata("NotLoopIV");
              }
            }
          }
        }

        // Annotate MemoryAddr that is used in "MemoryStartLoad"
        if(auto* Load = dyn_cast<LoadInst>(&Instruction)){
          if(isAnnotated(Load, "MemoryStartLoad")){
            if(auto* GEP = dyn_cast<GEPOperator>(Load->getNextNode())){
              if(GEP->getOperand(0) == Load && GEP->getNumOperands() == 2){
                auto* MemAddrInstr = reinterpret_cast<llvm::Instruction*>(GEP->getOperand(1));
                MemAddrInstr->addAnnotationMetadata("MemAddress"); // MemAddrInstr->user_begin()
              }
            }
          }
        }
      }
    }


    ValueToValueMapTy  VMap;
    auto* FirstPreLoopBlock = L->getLoopPreheader();
    auto* LastPreLoopBlock = FirstPreLoopBlock;
    // Extract one Loop iteration to Preheader
    for(auto* BB : L->getBlocks()){
      auto* LastInstruction = &BB->getInstList().back();
        auto* Branch = dyn_cast<BranchInst>(LastInstruction);
        assert(Branch);
        auto* BBDash = CloneBasicBlock(BB, VMap, "_bounds_check", BB->getParent());
        VMap[BBDash] = BB;
        VMap[BB] = BBDash;
        for(auto& Inst : *BBDash){
          RemapInstruction(&Inst, VMap, RF_NoModuleLevelChanges | RF_IgnoreMissingLocals);
        }
        /*
        assumeIndexIsInBounds(BB);
        replaceBCIndexWithMax(BBDash, LB.IndexPointer, LB.MaxValue);
         */
        addBBDashToPreHeader(LastPreLoopBlock, BBDash, L);
        LastPreLoopBlock = BBDash;
    }

    // Analyze and fix PreLoop BoundsChecks
    auto* BBDash = FirstPreLoopBlock;
    do{
      auto* LastInstruction = &BBDash->getInstList().back();
      if(isAnnotated(LastInstruction, "wasmer_bounds_check")){
        auto* BB = reinterpret_cast<BasicBlock*>(VMap[BBDash].operator llvm::Value *());
        if(isVectorAccess(BBDash)){
          replaceBCIndexWithMax(BBDash, LB.IndexPointer, LB.MaxValue);
          assumeIndexIsInBounds(BB);
        }
      }
      BBDash = BBDash->getNextNode();
    }while(BBDash != LastPreLoopBlock);
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
    BBDash->moveAfter(LastPreLoopBlock);
    auto* BBDashBranch = dyn_cast<BranchInst>(&BBDash->getInstList().back());
    assert(BBDashBranch);
    BBDashBranch->setSuccessor(0, L->getHeader());
  }

  bool isVectorAccess(BasicBlock * BB){
    if(dyn_cast<LoadInst>(BB->getInstList().front().getNextNode())){
      return true;
    }
    return false;
  }

  void replaceBCIndexWithMax(BasicBlock *BB, Value*IndexPointer, Value* MaxValue) {
    for(auto&MemAddressInst : *BB){
      if(isAnnotated(&MemAddressInst, "MemAddress")){
        // TODO: Make sure only one instruction is annotated by MemAddress
        ICmpInst* BoundsCheckCompare = nullptr;
        // Check if after MemAddress, bounds check is performed
        if(auto* AddSize = dyn_cast<AddOperator>(MemAddressInst.getNextNode())){
          if(AddSize->getOperand(0) == &MemAddressInst){
            if(auto* LoadMaxMem = dyn_cast<LoadInst>(
                    MemAddressInst.getNextNode()->getNextNode())){
              if(isAnnotated(LoadMaxMem, "MaxMemoryLoad")){
                if(auto* ICmp = dyn_cast<ICmpInst>(MemAddressInst.getNextNode()->getNextNode()->getNextNode())){
                  // Compare of index and max bounds found
                  BoundsCheckCompare = ICmp;
                }
              }
            }
          }
        }


        if(BoundsCheckCompare){
          std::vector<llvm::Instruction*> CopiedInstructions;
          std::vector<llvm::Instruction*> InstructionsToCopy;
          std::unordered_map<llvm::Instruction*, size_t> OriginalInstructionMap;
          InstructionsToCopy.push_back(&MemAddressInst);
          CopiedInstructions.push_back(MemAddressInst.clone());
          CopiedInstructions.back()->insertAfter(&MemAddressInst);
          OriginalInstructionMap.emplace(&MemAddressInst, 0);


          // Collect all Instructions that need to be copied
          for(size_t CopyStartIdx = 0; CopyStartIdx != InstructionsToCopy.size(); ++CopyStartIdx){
            auto* Next = InstructionsToCopy.at(CopyStartIdx);
            for(auto* OpIt = Next->op_begin(); OpIt != Next->op_end(); ++OpIt){
              if(auto* OpInst = dyn_cast<llvm::Instruction>(*OpIt)){
                if(!dyn_cast<LoadInst>(OpInst)){
                  auto* Cloned = OpInst->clone();
                  OriginalInstructionMap.emplace(OpInst, InstructionsToCopy.size());
                  InstructionsToCopy.push_back(OpInst);
                  Cloned->insertAfter(OpInst);
                  CopiedInstructions.push_back(Cloned);
                }
              }
            }
          }

          // Update Operators in Copied Instructions
          for(auto ItOg = InstructionsToCopy.rbegin(); ItOg != InstructionsToCopy.rend(); ++ItOg){
            auto* OgInst = *ItOg;
            auto Index = OriginalInstructionMap.find(*ItOg)->second;
            auto* CpyInst = CopiedInstructions.at(Index);
            for(size_t OpIndex = 0; OpIndex < CpyInst->getNumOperands(); ++OpIndex){
              auto* Operand = CpyInst->getOperand(OpIndex);
              if(auto* Load = dyn_cast<LoadInst>(Operand)){
                if(Load->getOperand(0) == IndexPointer){
                  // Replace Index with Max Value
                  CpyInst->setOperand(OpIndex, MaxValue);
                }
              }else if(auto* Inst = dyn_cast<llvm::Instruction>(Operand)){
                CpyInst->setOperand(OpIndex, CopiedInstructions.at(OriginalInstructionMap.find(Inst)->second));
              }
            }
          }

          // Use Max Index value for bounds check
          BoundsCheckCompare->setOperand(0, CopiedInstructions.front());
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