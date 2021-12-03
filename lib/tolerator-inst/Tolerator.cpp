

#include "llvm/IR/BasicBlock.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"
#include "Tolerator.h"


using namespace llvm;
using tolerator::Tolerator;


namespace tolerator {

char Tolerator::ID = 0;

}


bool
Tolerator::runOnModule(Module& m) {
  auto& context = m.getContext();

  // This analysis just prints a message when the program starts or exits.
  // You should modify this code as you see fit.
  auto* voidTy = Type::getVoidTy(context);

  auto helloworld = m.getOrInsertFunction("ToLeRaToR_helloworld", voidTy);
  //appendToGlobalCtors(m, llvm::cast<Function>(helloworld.getCallee()), 0);

  auto goodbyeworld = m.getOrInsertFunction("ToLeRaToR_goodbyeworld", voidTy);


  std::vector<Type*> params;
  params.push_back(Type::getInt32Ty(context));
  auto exit = m.getOrInsertFunction("exit", FunctionType::get(Type::getVoidTy(context), params, false));

  params.clear();
  params.push_back(Type::getInt8PtrTy(context));
  params.push_back(Type::getInt32Ty(context));
  params.push_back(Type::getInt64Ty(context));
  auto PushPtr = m.getOrInsertFunction("ToLeRaToR_PushPtr", FunctionType::get(Type::getVoidTy(context), params, false));
  auto PopPtr = m.getOrInsertFunction("ToLeRaToR_PopPtr", FunctionType::get(Type::getVoidTy(context), params, false));

  params.clear();
  params.push_back(Type::getInt8PtrTy(context));
  params.push_back(Type::getInt64Ty(context));
  auto PostMalloc = m.getOrInsertFunction("ToLeRaToR_PostMalloc", FunctionType::get(Type::getVoidTy(context), params, false));
  auto PushGlobal = m.getOrInsertFunction("ToLeRaToR_PushGlobal", FunctionType::get(Type::getVoidTy(context), params, false));
  auto IsValidPtr = m.getOrInsertFunction("ToLeRaToR_IsValidPtr", FunctionType::get(Type::getInt8Ty(context), params, false));

  params.clear();
  params.push_back(Type::getInt8PtrTy(context));
  auto IsValidFree = m.getOrInsertFunction("ToLeRaToR_IsValidFree", FunctionType::get(Type::getInt8Ty(context), params, false));
  auto MyFree = m.getOrInsertFunction("ToLeRaToR_MyFree", FunctionType::get(Type::getVoidTy(context), params, false));

  std::vector<AllocaInst*> allocaInstr;
  std::vector<LoadInst*> loadInstr;
  std::vector<StoreInst*> storeInstr;
  std::vector<CallInst*> callInstr;
  std::vector<Instruction*> divInstr;

  for (auto& func : m) {
    for (auto& bb : func) {
      for (auto& instr : bb) {
        auto opCode = instr.getOpcode();
        switch (opCode) {
          case llvm::Instruction::UDiv:
          case llvm::Instruction::SDiv:
          case llvm::Instruction::FDiv:
          case llvm::Instruction::URem:
          case llvm::Instruction::SRem:
          case llvm::Instruction::FRem:
            divInstr.push_back(&instr);
            break;
          case llvm::Instruction::Alloca:
            allocaInstr.push_back((AllocaInst*)&instr);
            break;
          case llvm::Instruction::Call:
            callInstr.push_back((CallInst*)&instr);
            break;
          case llvm::Instruction::Store:
            storeInstr.push_back((StoreInst*)&instr);
            break;
          case llvm::Instruction::Load:
            loadInstr.push_back((LoadInst*)&instr);
            break;
        }
      }
    }
  }

  // Handle divide by zero
  for (auto instr : divInstr) {
    auto divisor = instr->getOperand(1);

    IRBuilder<> Builder(instr);
    Value* isZero;
    if (instr->getOpcode() == llvm::Instruction::FDiv || instr->getOpcode() == llvm::Instruction::FRem) {
      auto zero_f = llvm::ConstantFP::get(divisor->getType(), 0);
      isZero = Builder.CreateICmpEQ(divisor, zero_f);
    } else {
      auto zero_i = llvm::ConstantInt::get(divisor->getType(), 0);
      isZero = Builder.CreateICmpEQ(divisor, zero_i);
    }

    auto trueBlock = SplitBlockAndInsertIfThen(isZero, instr, false);

    auto printLogZero = m.getOrInsertFunction("ToLeRaToR_logzero", voidTy);
    IRBuilder<> TrueBuilder(trueBlock);
    TrueBuilder.CreateCall(printLogZero);

    if (Tolerator::type == AnalysisType::LOGGING || Tolerator::type == AnalysisType::IGNORING) {
      TrueBuilder.CreateCall(exit, ConstantInt::get(Type::getInt32Ty(context), -1, true));
    }

    if (Tolerator::type == AnalysisType::DEFAULTING) {
      IRBuilder<> PhiBuilder(instr);

      auto dividend = instr->getOperand(0);
      auto divisor = instr->getOperand(1);
      auto type = instr->getType();

      auto phiDenom = PhiBuilder.CreatePHI(type, 2);
      auto phiNumer = PhiBuilder.CreatePHI(type, 2);

      phiDenom->addIncoming(Constant::getNullValue(dividend->getType()), trueBlock->getParent());
      phiDenom->addIncoming(dividend, trueBlock->getParent()->getSinglePredecessor());

      if (divisor->getType()->isIntegerTy()) {
        phiNumer->addIncoming(ConstantInt::get(divisor->getType(), 1), trueBlock->getParent());
      } else {
        phiNumer->addIncoming(ConstantFP::get(divisor->getType(), 1), trueBlock->getParent());
      }
      phiNumer->addIncoming(divisor, trueBlock->getParent()->getSinglePredecessor());

      instr->setOperand(0, phiDenom);
      instr->setOperand(1, phiNumer);
    }

    if (Tolerator::type == AnalysisType::BYPASSING) {
      auto retTy = instr->getParent()->getParent()->getReturnType();

      if (retTy->isVoidTy()) {
        TrueBuilder.CreateRetVoid();
      } else {
        auto ret = Constant::getNullValue(retTy);
        TrueBuilder.CreateRet(ret);
      }

      // Remove the existing terminator and substitute the new ret
      trueBlock->eraseFromParent();
    }
  }

  // Handle bad free's and track mallocs
  for (auto instr : callInstr) {
    auto fn = instr->getCalledFunction();
    if (!fn) {
      fn = dyn_cast<Function>(instr->getCalledValue()->stripPointerCasts());
    }

    if (fn->getName().equals("malloc")) {
      CallSite CS(instr);
      auto arg = CS.getArgument(0);

      IRBuilder<> Builder(instr->getNextNode());
      Builder.CreateCall(PostMalloc, {(Value*) instr, (Value*)arg});
    }

    if (fn->getName().equals("free")) {
      CallSite CS(instr);
      auto arg = CS.getArgument(0);

      IRBuilder<> Builder(instr);
      auto valid = Builder.CreateCall(IsValidFree, {(Value*)arg});
      auto cmp = Builder.CreateICmpEQ(valid, ConstantInt::get(valid->getType(), 0));

      auto invalidFreeBlock = SplitBlockAndInsertIfThen(cmp, &*Builder.GetInsertPoint(), false);

      auto logfree = m.getOrInsertFunction("ToLeRaToR_logfree", voidTy);
      IRBuilder<> TrueBuilder(invalidFreeBlock);
      TrueBuilder.CreateCall(logfree);

      if (Tolerator::type == AnalysisType::LOGGING) {
        TrueBuilder.CreateCall(exit, ConstantInt::get(Type::getInt32Ty(context), -1, true));
      }

      if (Tolerator::type == AnalysisType::IGNORING || Tolerator::type == AnalysisType::DEFAULTING) {
        IRBuilder<> FreeBuilder(instr);
        FreeBuilder.CreateCall(MyFree, {arg});
        //instr->setCalledFunction(MyFree);
        instr->eraseFromParent();
      }

      if (Tolerator::type == AnalysisType::BYPASSING) {
        auto retTy = instr->getParent()->getParent()->getReturnType();
        if (retTy->isVoidTy()) {
          TrueBuilder.CreateRetVoid();
        } else {
          auto ret = Constant::getNullValue(retTy);
          TrueBuilder.CreateRet(ret);
        }
        invalidFreeBlock->eraseFromParent();
      }
    }
  }

  // Track stack-local allocation
  for (auto instr : allocaInstr) {
    auto parentFunc = instr->getParent()->getParent();
    auto count = instr->getArraySize();
    auto type = instr->getAllocatedType();
    auto size = m.getDataLayout().getTypeAllocSize(type);
    // IRBuilder inserts before instr, preserve SSA dom by inserting after alloca instr
    IRBuilder<> Builder(instr->getNextNode());

    auto casted = Builder.CreateBitCast(instr, Type::getInt8PtrTy(context));
    Builder.CreateCall(PushPtr, {(Value*) casted, count, ConstantInt::get(Type::getInt64Ty(context), size)});

    for (auto &bb : *parentFunc) {
      for (auto &i : bb) {
        if (i.getOpcode() == Instruction::Ret) {
          IRBuilder<> RetBuilder(&i);
          RetBuilder.CreateCall(PopPtr, {(Value*) casted, count, ConstantInt::get(Type::getInt64Ty(context), size)});
        }
      }
    }
  }

  // Track globals
  auto ctor = m.getOrInsertFunction("ToLeRaToR_ctor", voidTy);
  BasicBlock* entry = BasicBlock::Create(context, "entry", llvm::cast<Function>(ctor.getCallee()));
  {
    IRBuilder<> Builder(entry);

    for (auto &global : m.getGlobalList()) {
      if (global.getName().startswith("llvm")) {
        continue;
      }
      auto type = global.getValueType();
      auto size = m.getDataLayout().getTypeAllocSize(type);
      auto casted = Builder.CreateBitCast(&global, Type::getInt8PtrTy(context));
      Builder.CreateCall(PushGlobal, {casted, ConstantInt::get(Type::getInt64Ty(context), size)});
    }

    Builder.CreateRetVoid();
  }
  appendToGlobalCtors(m, llvm::cast<Function>(helloworld.getCallee()), 0);
  appendToGlobalCtors(m, llvm::cast<Function>(ctor.getCallee()), 1);
  appendToGlobalDtors(m, llvm::cast<Function>(goodbyeworld.getCallee()), 0);

  // Track writes
  for (auto instr : storeInstr) {
    auto ptr = instr->getPointerOperand();
    auto val = instr->getValueOperand();

    // If the pointer source is an alloca, it cannot be a bad write
    if (!dyn_cast<AllocaInst>(ptr)) {
      auto type = val->getType();
      auto size = m.getDataLayout().getTypeAllocSize(type);

      IRBuilder<> Builder(instr);
      auto casted = Builder.CreateBitCast(ptr, Type::getInt8PtrTy(context));
      auto valid = Builder.CreateCall(IsValidPtr, {casted, ConstantInt::get(Type::getInt64Ty(context), size)});
      auto cmp = Builder.CreateICmpEQ(valid, ConstantInt::get(valid->getType(), 0));
      auto logwrite = m.getOrInsertFunction("ToLeRaToR_logwrite", voidTy);

      if (Tolerator::type == AnalysisType::IGNORING || Tolerator::type == AnalysisType::DEFAULTING) {

        Instruction* ThenBlock;
        Instruction* ElseBlock;
        SplitBlockAndInsertIfThenElse(cmp, instr->getNextNode(), &ThenBlock, &ElseBlock);
        instr->moveBefore(ElseBlock);

        IRBuilder<> TrueBuilder(ThenBlock);
        TrueBuilder.CreateCall(logwrite);

      } else {

        auto invalidStoreBlock = SplitBlockAndInsertIfThen(cmp, &*Builder.GetInsertPoint(), false);

        IRBuilder<> TrueBuilder(invalidStoreBlock);
        TrueBuilder.CreateCall(logwrite);

        if (Tolerator::type == AnalysisType::LOGGING) {
          TrueBuilder.CreateCall(exit, ConstantInt::get(Type::getInt32Ty(context), -1, true));
        }

        if (Tolerator::type == AnalysisType::BYPASSING) {
          auto retTy = instr->getParent()->getParent()->getReturnType();
          if (retTy->isVoidTy()) {
            TrueBuilder.CreateRetVoid();
          } else {
            auto ret = Constant::getNullValue(retTy);
            TrueBuilder.CreateRet(ret);
          }
          invalidStoreBlock->eraseFromParent();
        }

      }
    }
  }

  // Track reads
  for (auto instr : loadInstr) {
    auto ptr = instr->getPointerOperand();

    if (!dyn_cast<AllocaInst>(ptr)) {
      auto type = instr->getType();
      auto size = m.getDataLayout().getTypeAllocSize(type);

      IRBuilder<> Builder(instr);
      auto casted = Builder.CreateBitCast(ptr, Type::getInt8PtrTy(context));
      auto valid = Builder.CreateCall(IsValidPtr, {casted, ConstantInt::get(Type::getInt64Ty(context), size)});
      auto cmp = Builder.CreateICmpEQ(valid, ConstantInt::get(valid->getType(), 0));
      auto logread = m.getOrInsertFunction("ToLeRaToR_logread", voidTy);

      if (Tolerator::type == AnalysisType::DEFAULTING) {

        auto splitOn = instr->getNextNode();
        Instruction* ThenBlock;
        Instruction* ElseBlock;
        SplitBlockAndInsertIfThenElse(cmp, splitOn, &ThenBlock, &ElseBlock);
        instr->moveBefore(ElseBlock);

        IRBuilder<> TrueBuilder(ThenBlock);
        TrueBuilder.CreateCall(logread);

        auto type = instr->getType();

        IRBuilder<> PhiBuilder(splitOn);
        auto phiValue = PhiBuilder.CreatePHI(type, 2);
        instr->replaceAllUsesWith(phiValue);

        phiValue->addIncoming(Constant::getNullValue(type), ThenBlock->getParent());
        phiValue->addIncoming(instr, ElseBlock->getParent());

      } else {

        auto invalidLoadBlock = SplitBlockAndInsertIfThen(cmp, &*Builder.GetInsertPoint(), false);

        IRBuilder<> TrueBuilder(invalidLoadBlock);
        TrueBuilder.CreateCall(logread);

        if (Tolerator::type == AnalysisType::LOGGING || Tolerator::type == AnalysisType::IGNORING) {
          TrueBuilder.CreateCall(exit, ConstantInt::get(Type::getInt32Ty(context), -1, true));
        }

        /*if (Tolerator::type == AnalysisType::DEFAULTING) {
          IRBuilder<> PhiBuilder(instr);

          auto value = instr->getOperand(0);
          auto type = value->getType();

          auto phiValue = PhiBuilder.CreatePHI(type, 2);

          phiValue->addIncoming(Constant::getNullValue(type), invalidLoadBlock->getParent());
          phiValue->addIncoming(value, invalidLoadBlock->getParent()->getSinglePredecessor());

          instr->setOperand(0, phiValue);
        }*/

        if (Tolerator::type == AnalysisType::BYPASSING) {
          auto retTy = instr->getParent()->getParent()->getReturnType();
          if (retTy->isVoidTy()) {
            TrueBuilder.CreateRetVoid();
          } else {
            auto ret = Constant::getNullValue(retTy);
            TrueBuilder.CreateRet(ret);
          }
          invalidLoadBlock->eraseFromParent();
        }

      }

    }
  }

  return true;
}
