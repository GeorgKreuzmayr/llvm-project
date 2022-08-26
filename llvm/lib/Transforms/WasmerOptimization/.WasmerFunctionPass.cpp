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

using namespace llvm;

namespace {
struct WasmerFunctionPass : public FunctionPass {
  static char ID;
  WasmerFunctionPass() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    if(!F.getName().equals("wasmer_function__5")){
      return false;
    }

    for(auto&BasicBlock : F){
      for(auto&Instruction : BasicBlock){
        if(Instruction.getMetadata(10) != nullptr){
          if(auto*StringMetaData = dyn_cast<MDString>(
                  Instruction.getMetadata(10)->getOperand(0).get())) {
            if (StringMetaData->getString().equals("wasmer_bounds_check")) {
              // Found memory access with bounds check

              /* assume vec + i less than 2000
              if(Instruction.getOperand(0)->hasName()){
                if(Instruction.getOperand(0)->getName().equals("ptr_in_bounds_expect")){
                  auto* CmpInstruction = dyn_cast<ICmpInst>(Instruction.getPrevNode()->getPrevNode());
                  auto* VecAndI = dyn_cast<AddOperator>(CmpInstruction->getOperand(0));
                  ICmpInst *VecAndICmp = new ICmpInst(ICmpInst::ICMP_ULT, VecAndI, ConstantInt::get(VecAndI->getType(), 2000, false));
                  VecAndICmp->insertBefore(CmpInstruction);
                  assumeCMPIsTrue(VecAndICmp);
                }
              }
              */

              /* assume ptr_in_bounds_expect == true */
              auto *Prev = Instruction.getPrevNode();
              while (!dyn_cast<ICmpInst>(Prev)) {
                Prev->dump();
                Prev = Prev->getPrevNode();
              }
              // Test
              // Cmp Instruction for bounds check
              auto *ICMPInst = dyn_cast<ICmpInst>(Prev);
              assumeCMPIsTrue(ICMPInst);
              /* */
            }
          }
        }
      }
    }
    return true;
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
  */