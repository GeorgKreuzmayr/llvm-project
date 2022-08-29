#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/Support/raw_ostream.h"

#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/MemorySSA.h"
#include <iostream>

using namespace llvm;

namespace {
struct WasmerFunctionPass : public FunctionPass {
  static char ID;
  WasmerFunctionPass() : FunctionPass(ID) {}

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

  bool runOnFunction(Function &F) override {
    if(!F.getName().equals("wasmer_function__5")){
      return false;
    }
    std::vector<AllocaInst*> Allocas;
    Instruction* MemoryStart = nullptr;
    Instruction* MaxMemory = nullptr;
    auto& ctx = F.getContext();
    for(auto&BasicBlock : F){
      for(auto&Instruction : BasicBlock){
        if(auto* Alloca = dyn_cast<AllocaInst>(&Instruction)){
          Alloca->addAnnotationMetadata("LocalVariable");
          Allocas.push_back(Alloca);
        }

        if(auto* Load = dyn_cast<LoadInst>(&Instruction)){
          if(Load->getOperand(0) == MaxMemory){
            Load->addAnnotationMetadata("MaxMemoryLoad");
          }
          if(Load->getOperand(0) == MemoryStart){
            Load->addAnnotationMetadata("MemoryStartLoad");
          }
        }

        if(auto* Store = dyn_cast<StoreInst>(&Instruction)){
          auto* StoreDest = Store->getOperand(1);
          if(StoreDest == MaxMemory){
            // Store to Max Mem
            assert(false);
          }

          for(auto* Alloca : Allocas){
            if(Alloca == StoreDest){
              if(isAnnotated(Alloca, "InitialStore")){
                if(!isAnnotated(Alloca, "Store")){
                  Alloca->addAnnotationMetadata("Store");
                }
              }else{
                Alloca->addAnnotationMetadata("InitialStore");
              }
            }
          }
        }

        if(auto* GEP = dyn_cast<GetElementPtrInst>(&Instruction)){
          if(GEP->getNumOperands() == 2){
            if(GEP->getOperand(0) == F.getArg(0)){
              if(GEP->getOperand(1) == ConstantInt::get(IntegerType::getInt32Ty(ctx), 180)){
                auto* Next = GEP->getNextNode()->getNextNode();
                MemoryStart = Next;
                if(Next->getType() == PointerType::get(PointerType::getInt8PtrTy(ctx), 0)){
                  MemoryStart = Next;
                  MemoryStart->dump();
                  for(auto It = MemoryStart->use_begin(); It != MemoryStart->use_end(); ++It){
                    auto& A = *It;

                    auto U = A.getUser();
                    std::cerr << "Mem Start Pooint Use" << std::endl;

                    if(auto* Used = reinterpret_cast<llvm::Instruction*>(A.get())){
                      Used->dump();
                    }
                    if(auto* User = reinterpret_cast<llvm::Instruction*>(U)){
                      User->dump();
                    }
                  }
                  MemoryStart->addAnnotationMetadata("MemoryStartPointer");
                }
                Next = Next->getNextNode();
                if(Next->getType() == PointerType::getInt64PtrTy(ctx)){
                  MaxMemory = Next;
                  MaxMemory->addAnnotationMetadata("MaxMemoryPointer");
                }
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
}  // end of anonymous namespace

char WasmerFunctionPass::ID = 0;
static RegisterPass<WasmerFunctionPass> X("wasmer-function", "Hello World Pass",
                             false /* Only looks at CFG */,
                             false /* Analysis Pass */);


static RegisterStandardPasses Y(
    PassManagerBuilder::EP_EarlyAsPossible,
    [](const PassManagerBuilder &Builder,
       legacy::PassManagerBase &PM) { PM.add(new WasmerFunctionPass()); });

void assertCmpIsTrue(){

}

/*
OLD CODE

 ** CMPARE INDEX < 20000 **
 *
if(auto* Load = dyn_cast<LoadInst>(ItInst)){
  if(Load->getOperand(0)->getName().equals("local")){
    Function *AssumeIntrinsic =
        Intrinsic::getDeclaration(Load->getModule(), Intrinsic::assume);
    ICmpInst *LoadLessThanBound = new ICmpInst(ICmpInst::ICMP_ULT, Load, ConstantInt::get(Load->getType(), 2000000, false));
    LoadLessThanBound->insertAfter(Load);
    CallInst *CI = CallInst::Create(AssumeIntrinsic, {LoadLessThanBound});
    CI->insertAfter(LoadLessThanBound);
    // AssumptionCache AC = getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);
    // AC.registerAssumption(CI);
    Load->dump();
  }
}

 ** PRINT WHOLE PREV FUNCTION **
 auto* It2 = ItInst;
 while(It2->getNextNode()){
   It2->dump();
   It2 = It2->getNextNode();
 }
 dd.dump();

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
// Test
// Cmp Instruction for bounds check
auto *ICMPInst = dyn_cast<ICmpInst>(Prev);
assumeCMPIsTrue(ICMPInst);
}
  */