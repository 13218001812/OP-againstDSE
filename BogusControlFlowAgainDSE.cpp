//===- BogusControlFlow.cpp - BogusControlFlow Obfuscation
//pass-------------------------===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------------------===//
//
// This file implements BogusControlFlow's pass, inserting bogus control flow.
// It adds bogus flow to a given basic block this way:
//
// Before :
// 	         		     entry
//      			       |
//  	    	  	 ______v______
//   	    		|   Original  |
//   	    		|_____________|
//             		       |
// 		        	       v
//		        	     return
//
// After :
//           		     entry
//             		       |
//            		   ____v_____
//      			  |condition*| (false)
//           		  |__________|----+
//           		 (true)|          |
//             		       |          |
//           		 ______v______    |
// 		        +-->|   Original* |   |
// 		        |   |_____________| (true)
// 		        |   (false)|    !-----------> return
// 		        |    ______v______    |
// 		        |   |   Altered   |<--!
// 		        |   |_____________|
// 		        |__________|
//
//  * The results of these terminator's branch's conditions are always true, but
//  these predicates are
//    opacificated. For this, we declare two global values: x and y, and replace
//    the FCMP_TRUE predicate with (y < 10 || x * (x + 1) % 2 == 0) (this could
//    be improved, as the global values give a hint on where are the opaque
//    predicates)
//
//  The altered bloc is a copy of the original's one with junk instructions
//  added accordingly to the type of instructions we found in the bloc
//
//  Each basic block of the function is choosen if a random number in the range
//  [0,100] is smaller than the choosen probability rate. The default value
//  is 30. This value can be modify using the option -boguscf-prob=[value].
//  Value must be an integer in the range [0, 100], otherwise the default value
//  is taken. Exemple: -boguscf -boguscf-prob=60
//
//  The pass can also be loop many times on a function, including on the basic
//  blocks added in a previous loop. Be careful if you use a big probability
//  number and choose to run the loop many times wich may cause the pass to run
//  for a very long time. The default value is one loop, but you can change it
//  with -boguscf-loop=[value]. Value must be an integer greater than 1,
//  otherwise the default value is taken. Exemple: -boguscf -boguscf-loop=2
//
//
//  Defined debug types:
//  - "gen" : general informations
//  - "opt" : concerning the given options (parameter)
//  - "cfg" : printing the various function's cfg before transformation
//	      and after transformation if it has been modified, and all
//	      the functions at end of the pass, after doFinalization.
//
//  To use them all, simply use the -debug option.
//  To use only one of them, follow the pass' command by -debug-only=name.
//  Exemple, -boguscf -debug-only=cfg
//
//
//  Stats:
//  The following statistics will be printed if you use
//  the -stats command:
//
// a. Number of functions in this module
// b. Number of times we run on each function
// c. Initial number of basic blocks in this module
// d. Number of modified basic blocks
// e. Number of added basic blocks in this module
// f. Final number of basic blocks in this module
//
// file   : lib/Transforms/Obfuscation/BogusControlFlow.cpp
// date   : june 2012
// version: 1.0
// author : julie.michielin@gmail.com
// modifications: pjunod, Rinaldini Julien
// project: Obfuscator
// option : -boguscf
//
//===----------------------------------------------------------------------------------===//

#include "llvm/Transforms/Obfuscation/BogusControlFlow.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
// #include "llvm/ADT/Hashing.h"
#include <openssl/sha.h>
#include "llvm/IR/Verifier.h"
#include "llvm/Support/DynamicLibrary.h"
#include <city.h>

// Stats
#define DEBUG_TYPE "BogusControlFlow"
STATISTIC(NumFunction, "a. Number of functions in this module");
STATISTIC(NumTimesOnFunctions, "b. Number of times we run on each function");
STATISTIC(InitNumBasicBlocks,
          "c. Initial number of basic blocks in this module");
STATISTIC(NumModifiedBasicBlocks, "d. Number of modified basic blocks");
STATISTIC(NumAddedBasicBlocks,
          "e. Number of added basic blocks in this module");
STATISTIC(FinalNumBasicBlocks,
          "f. Final number of basic blocks in this module");

// Options for the pass
const int defaultObfRate = 70, defaultObfTime = 1;
const string defaultType = "hash";

static cl::opt<int>
    ObfProbRate("bcf_prob",
                cl::desc("Choose the probability [%] each basic blocks will be "
                         "obfuscated by the -bcf pass"),
                cl::value_desc("probability rate"), cl::init(defaultObfRate),
                cl::Optional);

static cl::opt<int>
    ObfTimes("bcf_loop",
             cl::desc("Choose how many time the -bcf pass loop on a function"),
             cl::value_desc("number of times"), cl::init(defaultObfTime),
             cl::Optional);
static cl::opt<int>
    FibNum("fibNum",
             cl::desc("Choose a fib number"),
             cl::value_desc("number"), cl::init(20),
             cl::Optional);

static cl::opt<string>
    ObfType("bcf_type",
             cl::desc("Choose which type of opaque predicates against symbolic execution "),
             cl::value_desc("type of opaque predicates"), cl::init(defaultType),
             cl::Optional);

namespace {
  
struct BogusControlFlow : public FunctionPass {
  static char ID; // Pass identification
  bool flag;
  SmallVector<AllocaInst *, 0> allocaInsts;
  BogusControlFlow() : FunctionPass(ID) {}
  BogusControlFlow(bool flag) : FunctionPass(ID) {
    this->flag = flag;
    BogusControlFlow();
  }

  /* runOnFunction
   *
   * Overwrite FunctionPass method to apply the transformation
   * to the function. See header for more details.
   */
  virtual bool runOnFunction(Function &F) {
        if (llvm::sys::DynamicLibrary::LoadLibraryPermanently("/home/zzz/cityhash/src/libcityhash.so")) {
        errs() << "Failed to load library ./libcityhash.so\n";
        return 1;
    }
    // Check if the percentage is correct
    if (ObfTimes <= 0) {
      errs() << "BogusControlFlow application number -bcf_loop=x must be x > 0";
      return false;
    }

    // Check if the number of applications is correct
    if (!((ObfProbRate > 0) && (ObfProbRate <= 100))) {
      errs() << "BogusControlFlow application basic blocks percentage "
                "-bcf_prob=x must be 0 < x <= 100";
      return false;
    }
    


       if(ObfType=="3n"){
    if(!F.getName().contains("intToStr")&&!F.getName().contains("CityHash")&&!F.getName().contains("fib")){
    
   
    
    if (toObfuscate(flag, &F, "bcf") && !F.getName().contains("fib")&&!F.getName().contains("CityHash")){
      
    //  findAllocInst(F.getEntryBlock()); 
    //  errs()<<allocaInsts.size()<<"allocainsts";
      
      bogus(F);
      
      // doF(*F.getParent(),fibFunction);
      return true;
    }
    }
    }
   if(ObfType=="fm"){
    
    if(!F.getName().contains("add")&&!F.getName().contains("CityHash")&&!F.getName().contains("fib")){



// Create function type: int add(int, int)
FunctionType *funcType = FunctionType::get(Type::getInt32Ty(F.getParent()->getContext()), 
                                           {Type::getInt32Ty(F.getParent()->getContext()), Type::getInt32Ty(F.getParent()->getContext())}, false);

// Create function and insert into module
Function *addFunction = Function::Create(funcType, Function::InternalLinkage, "add", F.getParent());

// Create the entry block and insert it into the function
BasicBlock *entry = BasicBlock::Create(F.getParent()->getContext(), "entry", addFunction);
IRBuilder<> builder(entry);

// Get function arguments
Function::arg_iterator args = addFunction->arg_begin();
Value *arg1 = &*args++;
arg1->setName("a");
Value *arg2 = &*args++;
arg2->setName("b");

// Define and initialize local variables
Value *x = builder.CreateAlloca(builder.getInt32Ty(), nullptr, "base");
Value *n = builder.CreateAlloca(builder.getInt32Ty(), nullptr, "exponent");
Value *mod = builder.CreateAlloca(builder.getInt32Ty(), nullptr, "mod");
Value *result = builder.CreateAlloca(builder.getInt32Ty(), nullptr, "result");

builder.CreateStore(arg1, x);
builder.CreateStore(builder.getInt32(2099), n);  // Use arg2 as exponent (assuming user inputs it)
builder.CreateStore(builder.getInt32(2099), mod); // Fixed modulus value
builder.CreateStore(builder.getInt32(1), result); // Initialize result to 1

// Create loop and end blocks
BasicBlock *loop = BasicBlock::Create(F.getParent()->getContext(), "loop", addFunction);
BasicBlock *end = BasicBlock::Create(F.getParent()->getContext(), "end", addFunction);
BasicBlock *start = BasicBlock::Create(F.getParent()->getContext(), "start", addFunction);
builder.CreateBr(start);
builder.SetInsertPoint(start);
// Load values
Value *xVal = builder.CreateLoad(builder.getInt32Ty(), x, "xVal");
Value *nValue = builder.CreateLoad(builder.getInt32Ty(), n, "nValue");
Value *modVal = builder.CreateLoad(builder.getInt32Ty(), mod, "modVal");

// Check if n == 0, if yes, jump to the end block
Value *nEqualZero = builder.CreateICmpEQ(nValue, builder.getInt32(0), "nEqualZero");
builder.CreateCondBr(nEqualZero, end, loop);

// Branch to loop
// builder.CreateBr(loop);
builder.SetInsertPoint(loop);

// Check if n is odd (n % 2 == 1)
Value *nMod2 = builder.CreateURem(nValue, builder.getInt32(2), "nMod2");
Value *isOdd = builder.CreateICmpEQ(nMod2, builder.getInt32(1), "isOdd");

// Create blocks for if-else structure
BasicBlock *ifBlock = BasicBlock::Create(F.getParent()->getContext(), "if", addFunction);
BasicBlock *elseBlock = BasicBlock::Create(F.getParent()->getContext(), "else", addFunction);
BasicBlock *contBlock = BasicBlock::Create(F.getParent()->getContext(), "cont", addFunction);

builder.CreateCondBr(isOdd, ifBlock, elseBlock);

// ifBlock: result = (result * x) % mod
builder.SetInsertPoint(ifBlock);
Value *resultVal = builder.CreateLoad(builder.getInt32Ty(), result, "result");
Value *tempMul = builder.CreateMul(resultVal, xVal, "tempMul");
Value *resultMod = builder.CreateURem(tempMul, modVal, "resultMod");
builder.CreateStore(resultMod, result);
builder.CreateBr(elseBlock);

// elseBlock: x = (x * x) % mod; n = n / 2
builder.SetInsertPoint(elseBlock);
Value *xSquared = builder.CreateMul(xVal, xVal, "xSquared");
Value *xNew = builder.CreateURem(xSquared, modVal, "xNew");
builder.CreateStore(xNew, x);
Value *nDiv2 = builder.CreateSDiv(nValue, builder.getInt32(2), "nDiv2");
builder.CreateStore(nDiv2, n);
builder.CreateBr(contBlock);

// Continue the loop
builder.SetInsertPoint(contBlock);
builder.CreateBr(start);

// End block: return result
builder.SetInsertPoint(end);
Value *finalResult = builder.CreateLoad(builder.getInt32Ty(), result, "finalResult");
builder.CreateRet(finalResult);

// Verify function
verifyFunction(*addFunction);

    
    if (toObfuscate(flag, &F, "bcf") && !F.getName().contains("fib")&&!F.getName().contains("CityHash")){
      
    //  findAllocInst(F.getEntryBlock()); 
     errs()<<allocaInsts.size()<<"allocainsts";
      
      bogus(F);
      
      doF(*F.getParent(),addFunction);
      return true;
    }
    }
    }

    if(ObfType=="fib"){
    if(!F.getName().contains("intToStr")&&!F.getName().contains("CityHash")&&!F.getName().contains("fib")){
    

ArrayType *arrayType = ArrayType::get(Type::getInt32Ty(F.getParent()->getContext()), 30);
GlobalVariable *memo = new GlobalVariable(*F.getParent(), arrayType, false, GlobalValue::PrivateLinkage, ConstantAggregateZero::get(arrayType), "memo");

// 创建fib函数的原型
FunctionType *fibFuncType = FunctionType::get(Type::getInt32Ty(F.getParent()->getContext()), {Type::getInt32Ty(F.getParent()->getContext())}, false);
Function *fibFunction = Function::Create(fibFuncType, Function::InternalLinkage, "fib", F.getParent());

// 创建fibonacci函数的入口块
BasicBlock *entryBlock = BasicBlock::Create(F.getParent()->getContext(), "entry", fibFunction);
BasicBlock *checkMemoBlock = BasicBlock::Create(F.getParent()->getContext(), "check_memo", fibFunction);
BasicBlock *recurseBlock = BasicBlock::Create(F.getParent()->getContext(), "recurse", fibFunction);
BasicBlock *returnBlock = BasicBlock::Create(F.getParent()->getContext(), "return", fibFunction);
IRBuilder<> Builder(entryBlock);
Builder.SetInsertPoint(entryBlock);

// 获取函数参数（n）
Argument *n = &*fibFunction->arg_begin();
n->setName("n");

// 检查 n <= 1，如果是，直接返回 n
Value *cond = Builder.CreateICmpSLE(n, Builder.getInt32(1), "cond");
Builder.CreateCondBr(cond, returnBlock, checkMemoBlock);

// 进入检查memo块，加载memo[n]的值，查看是否已经计算过
Builder.SetInsertPoint(checkMemoBlock);
Value *index = Builder.CreateZExtOrBitCast(n, Builder.getInt32Ty()); // 确保索引类型匹配
Value *memoPtr = Builder.CreateGEP(memo->getValueType(), memo, {Builder.getInt32(0), index}, "memoPtr");
Value *cachedValue = Builder.CreateLoad(memoPtr, "cachedValue");

// 如果memo[n] != 0，直接返回缓存结果
Value *isCached = Builder.CreateICmpNE(cachedValue, Builder.getInt32(0), "isCached");
Builder.CreateCondBr(isCached, returnBlock, recurseBlock);

// 在递归块，进行递归调用fibonacci(n-1)和fibonacci(n-2)
Builder.SetInsertPoint(recurseBlock);
Value *nMinus1 = Builder.CreateSub(n, Builder.getInt32(1), "nMinus1");
Value *nMinus2 = Builder.CreateSub(n, Builder.getInt32(2), "nMinus2");

// 递归调用fibonacci(n-1)
Value *fibNMinus1 = Builder.CreateCall(fibFunction, nMinus1, "fibNMinus1");

// 递归调用fibonacci(n-2)
Value *fibNMinus2 = Builder.CreateCall(fibFunction, nMinus2, "fibNMinus2");

// 将结果相加fib(n-1) + fib(n-2)
Value *result = Builder.CreateAdd(fibNMinus1, fibNMinus2, "result");

// 将结果存储到memo[n]
Builder.CreateStore(result, memoPtr);

// 跳转到returnBlock
Builder.CreateBr(returnBlock);

// 单一结束块：从缓存、递归返回或直接返回结果
Builder.SetInsertPoint(returnBlock);
PHINode *phi = Builder.CreatePHI(Type::getInt32Ty(F.getParent()->getContext()), 3, "returnVal");
phi->addIncoming(n, entryBlock);       // 当 n <= 1 时，返回 n
phi->addIncoming(cachedValue, checkMemoBlock); // 从缓存中返回结果
phi->addIncoming(result, recurseBlock); // 从递归计算中返回结果
Builder.CreateRet(phi);

// 验证函数是否正确
verifyFunction(*fibFunction);


    
    if (toObfuscate(flag, &F, "bcf") && !F.getName().contains("fib")&&!F.getName().contains("CityHash")){
      
    //  findAllocInst(F.getEntryBlock()); 
     errs()<<allocaInsts.size()<<"allocainsts";
      
      bogus(F);
      
      doF(*F.getParent(),fibFunction);
      return true;
    }
    }
    }


if(ObfType=="hash"){
    if(!F.getName().contains("intToStr")&&!F.getName().contains("CityHash")&&!F.getName().contains("fib")){
    
 
//cithhash
    std::vector<Type*> HashArgs = {Type::getInt32Ty(F.getParent()->getContext())};
    FunctionType* HashType = FunctionType::get(Type::getInt32Ty(F.getParent()->getContext()), HashArgs, false);
    Constant *IntToStrFun = F.getParent()->getOrInsertFunction("hashIntWithCityHash32", HashType);
    Function *IntToStrFunc= cast<Function>(IntToStrFun);

  
        // If fla annotations
    
    if (toObfuscate(flag, &F, "bcf") && !F.getName().contains("fib")&&!F.getName().contains("CityHash")){
      
    //  findAllocInst(F.getEntryBlock()); 
     errs()<<allocaInsts.size()<<"allocainsts";
      
      bogus(F);
      
      doF(*F.getParent(),IntToStrFunc);
      return true;
    }
    }
    }
if(ObfType=="default"){
    
    
        // If fla annotations
    
    if (toObfuscate(flag, &F, "bcf") ){
      
    //  findAllocInst(F.getEntryBlock()); 
     errs()<<allocaInsts.size()<<"allocainsts";
      
      bogus(F);
      
      doF(*F.getParent(),&F);
      return true;
    }
    
    }
    return false;
  } // end of runOnFunction()

  // find all inpout variables and local variables
  int findAllocInst(BasicBlock &BB) {
    Type *Int32Ty = Type::getInt32Ty(BB.getContext());
    for (Instruction &inst : BB) {
      if (AllocaInst *allocaInst = dyn_cast<AllocaInst>(&inst)) {
        if (allocaInst->getAllocatedType() != Int32Ty) {
          continue;
        }
        allocaInsts.emplace_back(allocaInst);
      }
    }
    return allocaInsts.size();
  }
  void bogus(Function &F) {
    // For statistics and debug
    ++NumFunction;
    int NumBasicBlocks = 0;
    bool firstTime = true; // First time we do the loop in this function
    bool hasBeenModified = false;
    DEBUG_WITH_TYPE("opt", errs() << "bcf: Started on function " << F.getName()
                                  << "\n");
    DEBUG_WITH_TYPE("opt",
                    errs() << "bcf: Probability rate: " << ObfProbRate << "\n");
    if (ObfProbRate < 0 || ObfProbRate > 100) {
      DEBUG_WITH_TYPE("opt", errs()
                                 << "bcf: Incorrect value,"
                                 << " probability rate set to default value: "
                                 << defaultObfRate << " \n");
      ObfProbRate = defaultObfRate;
    }
    DEBUG_WITH_TYPE("opt", errs()
                               << "bcf: How many times: " << ObfTimes << "\n");
    if (ObfTimes <= 0) {
      DEBUG_WITH_TYPE("opt", errs()
                                 << "bcf: Incorrect value,"
                                 << " must be greater than 1. Set to default: "
                                 << defaultObfTime << " \n");
      ObfTimes = defaultObfTime;
    }
    NumTimesOnFunctions = ObfTimes;
    int NumObfTimes = ObfTimes;

    // Real begining of the pass
    // Loop for the number of time we run the pass on the function
    do {
      DEBUG_WITH_TYPE("cfg", errs() << "bcf: Function " << F.getName()
                                    << ", before the pass:\n");
      DEBUG_WITH_TYPE("cfg", F.viewCFG());
      // Put all the function's block in a list
      std::list<BasicBlock *> basicBlocks;
      for (Function::iterator i = F.begin(); i != F.end(); ++i) {
        basicBlocks.push_back(&*i);
      }
      DEBUG_WITH_TYPE(
          "gen", errs() << "bcf: Iterating on the Function's Basic Blocks\n");

      while (!basicBlocks.empty()) {
        NumBasicBlocks++;
        // Basic Blocks' selection
        if ((int)llvm::cryptoutils->get_range(100) <= ObfProbRate) {
          DEBUG_WITH_TYPE("opt", errs() << "bcf: Block " << NumBasicBlocks
                                        << " selected. \n");
          hasBeenModified = true;
          ++NumModifiedBasicBlocks;
          NumAddedBasicBlocks += 3;
          FinalNumBasicBlocks += 3;
          // Add bogus flow to the given Basic Block (see description)
          BasicBlock *basicBlock = basicBlocks.front();
          if(ObfType=="3n") {addBogusFlow3n(basicBlock, F);}
          else{
          addBogusFlow(basicBlock, F);
          }
        } else {
          DEBUG_WITH_TYPE("opt", errs() << "bcf: Block " << NumBasicBlocks
                                        << " not selected.\n");
        }
        // remove the block from the list
        basicBlocks.pop_front();

        if (firstTime) { // first time we iterate on this function
          ++InitNumBasicBlocks;
          ++FinalNumBasicBlocks;
        }
      } // end of while(!basicBlocks.empty())
      DEBUG_WITH_TYPE("gen",
                      errs() << "bcf: End of function " << F.getName() << "\n");
      if (hasBeenModified) { // if the function has been modified
        DEBUG_WITH_TYPE("cfg", errs() << "bcf: Function " << F.getName()
                                      << ", after the pass: \n");
        DEBUG_WITH_TYPE("cfg", F.viewCFG());
      } else {
        DEBUG_WITH_TYPE("cfg", errs()
                                   << "bcf: Function's not been modified \n");
      }
      firstTime = false;
    } while (--NumObfTimes > 0);
  }

  /* addBogusFlow
   *
   * Add bogus flow to a given basic block, according to the header's
   * description
   */
  virtual void addBogusFlow(BasicBlock *basicBlock, Function &F) {

    // Split the block: first part with only the phi nodes and debug info and
    // terminator
    //                  created by splitBasicBlock. (-> No instruction)
    //                  Second part with every instructions from the original
    //                  block
    // We do this way, so we don't have to adjust all the phi nodes, metadatas
    // and so on for the first block. We have to let the phi nodes in the first
    // part, because they actually are updated in the second part according to
    // them.
    BasicBlock::iterator i1 = basicBlock->begin();
    if (basicBlock->getFirstNonPHIOrDbgOrLifetime())
      i1 = (BasicBlock::iterator)basicBlock->getFirstNonPHIOrDbgOrLifetime();
    Twine *var;
    var = new Twine("originalBB");
    BasicBlock *originalBB = basicBlock->splitBasicBlock(i1, *var);
    DEBUG_WITH_TYPE("gen", errs()
                               << "bcf: First and original basic blocks: ok\n");

    // Creating the altered basic block on which the first basicBlock will jump
    Twine *var3 = new Twine("alteredBB");
    BasicBlock *alteredBB = createAlteredBasicBlock(originalBB, *var3, &F);
    DEBUG_WITH_TYPE("gen", errs() << "bcf: Altered basic block: ok\n");

    // Now that all the blocks are created,
    // we modify the terminators to adjust the control flow.

    alteredBB->getTerminator()->eraseFromParent();
    basicBlock->getTerminator()->eraseFromParent();
    DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator removed from the altered"
                                  << " and first basic blocks\n");

    // Preparing a condition..
    // For now, the condition is an always true comparaison between 2 float
    // This will be complicated after the pass (in doFinalization())
    Value *LHS = ConstantFP::get(Type::getFloatTy(F.getContext()), 1.0);
    Value *RHS = ConstantFP::get(Type::getFloatTy(F.getContext()), 1.0);
    DEBUG_WITH_TYPE("gen", errs() << "bcf: Value LHS and RHS created\n");

    // The always true condition. End of the first block
    Twine *var4 = new Twine("condition");
    FCmpInst *condition =
        new FCmpInst(*basicBlock, FCmpInst::FCMP_TRUE, LHS, RHS, *var4);
    DEBUG_WITH_TYPE("gen", errs() << "bcf: Always true condition created\n");

    // Jump to the original basic block if the condition is true or
    // to the altered block if false.
    BranchInst::Create(originalBB, alteredBB, (Value *)condition, basicBlock);
    DEBUG_WITH_TYPE(
        "gen",
        errs() << "bcf: Terminator instruction in first basic block: ok\n");

    // The altered block loop back on the original one.
    BranchInst::Create(originalBB, alteredBB);
    DEBUG_WITH_TYPE(
        "gen", errs() << "bcf: Terminator instruction in altered block: ok\n");

    // The end of the originalBB is modified to give the impression that
    // sometimes it continues in the loop, and sometimes it return the desired
    // value (of course it's always true, so it always use the original
    // terminator..
    //  but this will be obfuscated too;) )

    // iterate on instruction just before the terminator of the originalBB
    BasicBlock::iterator i = originalBB->end();

    // Split at this point (we only want the terminator in the second part)
    Twine *var5 = new Twine("originalBBpart2");
    BasicBlock *originalBBpart2 = originalBB->splitBasicBlock(--i, *var5);
    DEBUG_WITH_TYPE("gen",
                    errs() << "bcf: Terminator part of the original basic block"
                           << " is isolated\n");
    // the first part go either on the return statement or on the begining
    // of the altered block.. So we erase the terminator created when splitting.
    originalBB->getTerminator()->eraseFromParent();
    // We add at the end a new always true condition
    Twine *var6 = new Twine("condition2");
    FCmpInst *condition2 =
        new FCmpInst(*originalBB, CmpInst::FCMP_TRUE, LHS, RHS, *var6);
    BranchInst::Create(originalBBpart2, alteredBB, (Value *)condition2,
                       originalBB);
    DEBUG_WITH_TYPE("gen", errs()
                               << "bcf: Terminator original basic block: ok\n");
    DEBUG_WITH_TYPE("gen", errs() << "bcf: End of addBogusFlow().\n");

  } // end of addBogusFlow()
//add Bogus Flow for 3n+1 conjecture
virtual void addBogusFlow3n(BasicBlock *basicBlock, Function &F) {
      BasicBlock::iterator i1 = basicBlock->begin();
    if (basicBlock->getFirstNonPHIOrDbgOrLifetime())
      i1 = (BasicBlock::iterator)basicBlock->getFirstNonPHIOrDbgOrLifetime();
    Twine *var;
    var = new Twine("originalBB");
    BasicBlock *originalBB = basicBlock->splitBasicBlock(i1, *var);
    DEBUG_WITH_TYPE("gen", errs()
                               << "bcf: First and original basic blocks: ok\n");

    // Creating the altered basic block on which the first basicBlock will jump
    Twine *var3 = new Twine("alteredBB");
    BasicBlock *alteredBB = createAlteredBasicBlock(originalBB, *var3, &F);
    DEBUG_WITH_TYPE("gen", errs() << "bcf: Altered basic block: ok\n");

    // Now that all the blocks are created,
    // we modify the terminators to adjust the control flow.

    alteredBB->getTerminator()->eraseFromParent();
    basicBlock->getTerminator()->eraseFromParent();
    DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator removed from the altered"
                                  << " and first basic blocks\n");
     IRBuilder<> Builder(F.getParent()->getContext());                             
    // FunctionType *FuncType = FunctionType::get(Builder.getInt32Ty(), Builder.getInt32Ty(), false);
    // Function *CollatzFunc = Function::Create(FuncType, Function::ExternalLinkage, "collatz", F.getParent());
    // BasicBlock *EntryBB = BasicBlock::Create(Context, "entry", CollatzFunc);
   Builder.SetInsertPoint(basicBlock);

// Get the function argument 'n'
// Argument *ArgN = &*CollatzFunc->arg_begin();
// ArgN->setName("n");

// Blocks for branching
BasicBlock *OddBB = BasicBlock::Create(F.getContext(), "odd",&F);
BasicBlock *EvenBB = BasicBlock::Create(F.getContext(), "even",&F);
BasicBlock *ContinueBB = BasicBlock::Create(F.getContext(), "continue",&F);
BasicBlock *ContinueBB1 = BasicBlock::Create(F.getContext(), "continue1",&F);
BasicBlock *StartBB = BasicBlock::Create(F.getContext(), "exit", &F);
BasicBlock *entryBB = BasicBlock::Create(F.getContext(), "entry", &F);
// Value *AllocaN = Builder.CreateAlloca(Builder.getInt32Ty(), nullptr, "n");
// Builder.CreateStore(Builder.getInt32(1041), AllocaN);

Builder.CreateBr(entryBB);


Builder.SetInsertPoint(entryBB);

    // Create variables n and i
    Value *n = Builder.CreateAlloca(Builder.getInt32Ty(), nullptr, "n");
    Value *i = Builder.CreateAlloca(Builder.getInt32Ty(), nullptr, "i");

    // Initialize n = 0 and i = 0
    Builder.CreateStore(Builder.getInt32(0), n);
    Builder.CreateStore(Builder.getInt32(0), i);

    // Create the loop condition block
    BasicBlock *loopCond = BasicBlock::Create(F.getContext(), "loopCond",&F);
    BasicBlock *loopBody = BasicBlock::Create(F.getContext(), "loopBody",&F);
    BasicBlock *loopEnd = BasicBlock::Create(F.getContext(), "loopEnd", &F);

    // Jump to loop condition block
    Builder.CreateBr(loopCond);

    // Loop condition: i < 1045
    Builder.SetInsertPoint(loopCond);
    llvm::Value *iVal = Builder.CreateLoad(i);
    llvm::Value *cond = Builder.CreateICmpSLT(iVal, Builder.getInt32(997));
    Builder.CreateCondBr(cond, loopBody, StartBB);

    // Loop body
    Builder.SetInsertPoint(loopBody);

    // Load i and check if even (i % 2 == 0)
    iVal = Builder.CreateLoad(i);
    llvm::Value *isEven = Builder.CreateICmpEQ(Builder.CreateURem(iVal, Builder.getInt32(2)), Builder.getInt32(0));

    // n += 3 if i is even, else n--
    llvm::BasicBlock *thenBlock = llvm::BasicBlock::Create(F.getContext(), "then", &F);
    llvm::BasicBlock *elseBlock = llvm::BasicBlock::Create(F.getContext(), "else", &F);
    llvm::BasicBlock *afterIf = llvm::BasicBlock::Create(F.getContext(), "afterIf", &F);
    
    Builder.CreateCondBr(isEven, thenBlock, elseBlock);

    // Then block: n += 3
    Builder.SetInsertPoint(thenBlock);
    llvm::Value *nVal = Builder.CreateLoad(n);
    llvm::Value *nAdd = Builder.CreateAdd(nVal, Builder.getInt32(3));
    Builder.CreateStore(nAdd, n);
    Builder.CreateBr(afterIf);

    // Else block: n--
    Builder.SetInsertPoint(elseBlock);
    nVal = Builder.CreateLoad(n);
    llvm::Value *nSub = Builder.CreateSub(nVal, Builder.getInt32(1));
    Builder.CreateStore(nSub, n);
    Builder.CreateBr(afterIf);

    // After if
    Builder.SetInsertPoint(afterIf);

    // i++
    iVal = Builder.CreateLoad(i);
    llvm::Value *iInc = Builder.CreateAdd(iVal, Builder.getInt32(1));
    Builder.CreateStore(iInc, i);
    Builder.CreateBr(loopCond);

    // Loop end
    // Builder.SetInsertPoint(loopEnd);

    // // Return n
    // nVal = Builder.CreateLoad(n);
    // builder.CreateRet(nVal);





// Load the value of 'n':

// Builder.CreateBr(StartBB);
Builder.SetInsertPoint(StartBB);
Value *ArgN = Builder.CreateLoad(Builder.getInt32Ty(), n, "n_load");
// Compare if n < 1
Value *Cond1 = Builder.CreateICmpSLT(ArgN, Builder.getInt32(1), "cmp1");
Builder.CreateCondBr(Cond1, alteredBB, ContinueBB);

Builder.SetInsertPoint(ContinueBB);
Value *Cond = Builder.CreateICmpEQ(ArgN, Builder.getInt32(1), "cmp2");
Builder.CreateCondBr(Cond, originalBB,ContinueBB1);

// Continue block
Builder.SetInsertPoint(ContinueBB1);

// Compare if n % 2 == 0
Value *Cond2 = Builder.CreateICmpEQ(
    Builder.CreateAnd(ArgN, Builder.getInt32(1)), 
    Builder.getInt32(0), "cmp3");
Builder.CreateCondBr(Cond2, EvenBB, OddBB);

// Even block
Builder.SetInsertPoint(EvenBB);
Value *EvenN = Builder.CreateLShr(ArgN, 1, "nshr");
Builder.CreateStore(EvenN, n);
Builder.CreateBr(StartBB);

// Odd block
Builder.SetInsertPoint(OddBB);
Value *OddN = Builder.CreateAdd(Builder.CreateMul(ArgN, Builder.getInt32(3), "mul"), Builder.getInt32(1), "add");
Builder.CreateStore(OddN, n);
Builder.CreateBr(StartBB);

// The altered block loops back to the original one.
BranchInst::Create(originalBB, alteredBB);
    DEBUG_WITH_TYPE(
        "gen", errs() << "bcf: Terminator instruction in altered block: ok\n");
    // Exit block
    // Builder.SetInsertPoint(ExitBB);
    // Builder.CreateRet(ArgN);

    // Verify the function
    // verifyFunction(*CollatzFunc);

    // // Print the generated IR
    // ModuleOb->print(outs(), nullptr);

    // delete ModuleOb;
    // return 0;
}



  /* createAlteredBasicBlock
   *
   * This function return a basic block similar to a given one.
   * It's inserted just after the given basic block.
   * The instructions are similar but junk instructions are added between
   * the cloned one. The cloned instructions' phi nodes, metadatas, uses and
   * debug locations are adjusted to fit in the cloned basic block and
   * behave nicely.
   */
  virtual BasicBlock *createAlteredBasicBlock(BasicBlock *basicBlock,
                                              const Twine &Name = "gen",
                                              Function *F = 0) {
    // Useful to remap the informations concerning instructions.
    ValueToValueMapTy VMap;
    BasicBlock *alteredBB = llvm::CloneBasicBlock(basicBlock, VMap, Name, F);
    DEBUG_WITH_TYPE("gen", errs() << "bcf: Original basic block cloned\n");
    // Remap operands.
    BasicBlock::iterator ji = basicBlock->begin();
    for (BasicBlock::iterator i = alteredBB->begin(), e = alteredBB->end();
         i != e; ++i) {
      // Loop over the operands of the instruction
      for (User::op_iterator opi = i->op_begin(), ope = i->op_end(); opi != ope;
           ++opi) {
        // get the value for the operand
        Value *v = MapValue(*opi, VMap, RF_None, 0);
        if (v != 0) {
          *opi = v;
          DEBUG_WITH_TYPE("gen",
                          errs() << "bcf: Value's operand has been setted\n");
        }
      }
      DEBUG_WITH_TYPE("gen", errs() << "bcf: Operands remapped\n");
      // Remap phi nodes' incoming blocks.
      if (PHINode *pn = dyn_cast<PHINode>(i)) {
        for (unsigned j = 0, e = pn->getNumIncomingValues(); j != e; ++j) {
          Value *v = MapValue(pn->getIncomingBlock(j), VMap, RF_None, 0);
          if (v != 0) {
            pn->setIncomingBlock(j, cast<BasicBlock>(v));
          }
        }
      }
      DEBUG_WITH_TYPE("gen", errs() << "bcf: PHINodes remapped\n");
      // Remap attached metadata.
      SmallVector<std::pair<unsigned, MDNode *>, 4> MDs;
      i->getAllMetadata(MDs);
      DEBUG_WITH_TYPE("gen", errs() << "bcf: Metadatas remapped\n");
      // important for compiling with DWARF, using option -g.
      i->setDebugLoc(ji->getDebugLoc());
      ji++;
      DEBUG_WITH_TYPE("gen", errs()
                                 << "bcf: Debug information location setted\n");

    } // The instructions' informations are now all correct

    DEBUG_WITH_TYPE("gen",
                    errs() << "bcf: The cloned basic block is now correct\n");
    DEBUG_WITH_TYPE(
        "gen",
        errs() << "bcf: Starting to add junk code in the cloned bloc...\n");

    // add random instruction in the middle of the bloc. This part can be
    // improve
    for (BasicBlock::iterator i = alteredBB->begin(), e = alteredBB->end();
         i != e; ++i) {
      // in the case we find binary operator, we modify slightly this part by
      // randomly insert some instructions
      if (i->isBinaryOp()) { // binary instructions
        unsigned opcode = i->getOpcode();
        BinaryOperator *op, *op1 = NULL;
        Twine *var = new Twine("_");
        // treat differently float or int
        // Binary int
        if (opcode == Instruction::Add || opcode == Instruction::Sub ||
            opcode == Instruction::Mul || opcode == Instruction::UDiv ||
            opcode == Instruction::SDiv || opcode == Instruction::URem ||
            opcode == Instruction::SRem || opcode == Instruction::Shl ||
            opcode == Instruction::LShr || opcode == Instruction::AShr ||
            opcode == Instruction::And || opcode == Instruction::Or ||
            opcode == Instruction::Xor) {
          for (int random = (int)llvm::cryptoutils->get_range(10); random < 10;
               ++random) {
            switch (llvm::cryptoutils->get_range(4)) { // to improve
            case 0:                                    // do nothing
              break;
            case 1:
              op = BinaryOperator::CreateNeg(i->getOperand(0), *var, &*i);
              op1 = BinaryOperator::Create(Instruction::Add, op,
                                           i->getOperand(1), "gen", &*i);
              break;
            case 2:
              op1 = BinaryOperator::Create(Instruction::Sub, i->getOperand(0),
                                           i->getOperand(1), *var, &*i);
              op = BinaryOperator::Create(Instruction::Mul, op1,
                                          i->getOperand(1), "gen", &*i);
              break;
            case 3:
              op = BinaryOperator::Create(Instruction::Shl, i->getOperand(0),
                                          i->getOperand(1), *var, &*i);
              break;
            }
          }
        }
        // Binary float
        if (opcode == Instruction::FAdd || opcode == Instruction::FSub ||
            opcode == Instruction::FMul || opcode == Instruction::FDiv ||
            opcode == Instruction::FRem) {
          for (int random = (int)llvm::cryptoutils->get_range(10); random < 10;
               ++random) {
            switch (llvm::cryptoutils->get_range(3)) { // can be improved
            case 0:                                    // do nothing
              break;
            case 1:
              op = BinaryOperator::CreateFNeg(i->getOperand(0), *var, &*i);
              op1 = BinaryOperator::Create(Instruction::FAdd, op,
                                           i->getOperand(1), "gen", &*i);
              break;
            case 2:
              op = BinaryOperator::Create(Instruction::FSub, i->getOperand(0),
                                          i->getOperand(1), *var, &*i);
              op1 = BinaryOperator::Create(Instruction::FMul, op,
                                           i->getOperand(1), "gen", &*i);
              break;
            }
          }
        }
        if (opcode == Instruction::ICmp) { // Condition (with int)
          ICmpInst *currentI = (ICmpInst *)(&i);
          switch (llvm::cryptoutils->get_range(3)) { // must be improved
          case 0:                                    // do nothing
            break;
          case 1:
            currentI->swapOperands();
            break;
          case 2: // randomly change the predicate
            switch (llvm::cryptoutils->get_range(10)) {
            case 0:
              currentI->setPredicate(ICmpInst::ICMP_EQ);
              break; // equal
            case 1:
              currentI->setPredicate(ICmpInst::ICMP_NE);
              break; // not equal
            case 2:
              currentI->setPredicate(ICmpInst::ICMP_UGT);
              break; // unsigned greater than
            case 3:
              currentI->setPredicate(ICmpInst::ICMP_UGE);
              break; // unsigned greater or equal
            case 4:
              currentI->setPredicate(ICmpInst::ICMP_ULT);
              break; // unsigned less than
            case 5:
              currentI->setPredicate(ICmpInst::ICMP_ULE);
              break; // unsigned less or equal
            case 6:
              currentI->setPredicate(ICmpInst::ICMP_SGT);
              break; // signed greater than
            case 7:
              currentI->setPredicate(ICmpInst::ICMP_SGE);
              break; // signed greater or equal
            case 8:
              currentI->setPredicate(ICmpInst::ICMP_SLT);
              break; // signed less than
            case 9:
              currentI->setPredicate(ICmpInst::ICMP_SLE);
              break; // signed less or equal
            }
            break;
          }
        }
        if (opcode == Instruction::FCmp) { // Conditions (with float)
          FCmpInst *currentI = (FCmpInst *)(&i);
          switch (llvm::cryptoutils->get_range(3)) { // must be improved
          case 0:                                    // do nothing
            break;
          case 1:
            currentI->swapOperands();
            break;
          case 2: // randomly change the predicate
            switch (llvm::cryptoutils->get_range(10)) {
            case 0:
              currentI->setPredicate(FCmpInst::FCMP_OEQ);
              break; // ordered and equal
            case 1:
              currentI->setPredicate(FCmpInst::FCMP_ONE);
              break; // ordered and operands are unequal
            case 2:
              currentI->setPredicate(FCmpInst::FCMP_UGT);
              break; // unordered or greater than
            case 3:
              currentI->setPredicate(FCmpInst::FCMP_UGE);
              break; // unordered, or greater than, or equal
            case 4:
              currentI->setPredicate(FCmpInst::FCMP_ULT);
              break; // unordered or less than
            case 5:
              currentI->setPredicate(FCmpInst::FCMP_ULE);
              break; // unordered, or less than, or equal
            case 6:
              currentI->setPredicate(FCmpInst::FCMP_OGT);
              break; // ordered and greater than
            case 7:
              currentI->setPredicate(FCmpInst::FCMP_OGE);
              break; // ordered and greater than or equal
            case 8:
              currentI->setPredicate(FCmpInst::FCMP_OLT);
              break; // ordered and less than
            case 9:
              currentI->setPredicate(FCmpInst::FCMP_OLE);
              break; // ordered or less than, or equal
            }
            break;
          }
        }
      }
    }
    return alteredBB;
  } // end of createAlteredBasicBlock()

 

  /* doFinalization
   *
   * Overwrite FunctionPass method to apply the transformations to the whole
   * module. This part obfuscate all the always true predicates of the module.
   * More precisely, the condition which predicate is FCMP_TRUE.
   * It also remove all the functions' basic blocks' and instructions' names.
   */
  bool doF(Module &M,Function *IntToStrFunc) {

    // In this part we extract all always-true predicate and replace them with
    // opaque predicate: For this, we declare two global values: x and y, and
    // replace the FCMP_TRUE predicate with (y < 10 || x * (x + 1) % 2 == 0) A
    // better way to obfuscate the predicates would be welcome. In the meantime
    // we will erase the name of the basic blocks, the instructions and the
    // functions.
    DEBUG_WITH_TYPE("gen", errs() << "bcf: Starting doFinalization...\n");

    //  The global values
    Twine *varX = new Twine("x");
    Twine *varY = new Twine("y");
    Value *x1 = ConstantInt::get(Type::getInt32Ty(M.getContext()), 0, false);
    Value *y1 = ConstantInt::get(Type::getInt32Ty(M.getContext()), 0, false);

    GlobalVariable *x =
        new GlobalVariable(M, Type::getInt32Ty(M.getContext()), false,
                           GlobalValue::CommonLinkage, (Constant *)x1, *varX);
    GlobalVariable *y =
        new GlobalVariable(M, Type::getInt32Ty(M.getContext()), false,
                           GlobalValue::CommonLinkage, (Constant *)y1, *varY);

    std::vector<Instruction *> toEdit, toDelete;
    BinaryOperator *op, *op1 = NULL;
    LoadInst *opX, *opY, *opY1;
    ICmpInst *condition, *condition2;


    // FunctionType *hashFunctionType = FunctionType::get(Type::getInt32Ty(M.getContext()), {Type::getInt32Ty(M.getContext())}, false);
    // Function *hashFunction = Function::Create(hashFunctionType, Function::ExternalLinkage, "hash_function", &M);

    // // // // 定义 hash_function
    // BasicBlock *entry = BasicBlock::Create(M.getContext(), "entry", hashFunction);
    // IRBuilder<> builder(entry);

    // // // hash_function 的实现：返回输入参数本身
    // // // Function::arg_iterator args = hashFunction->arg_begin();
    // // // Value *input = &*args;
    // // // input->setName("input");
    // builder.CreateRet(ConstantInt::get(Type::getInt32Ty(M.getContext()), 1, false));
    // hashFunction->print(outs(), nullptr);




    // LLVMContext Context;
    // Module *M = new Module("my_module", Context);




    // Looking for the conditions and branches to transform
    for (Module::iterator mi = M.begin(), me = M.end(); mi != me; ++mi) {
      for (Function::iterator fi = mi->begin(), fe = mi->end(); fi != fe;
           ++fi) {
        // fi->setName("");
        TerminatorInst *tbb = fi->getTerminator();
        if (tbb->getOpcode() == Instruction::Br) {
          BranchInst *br = (BranchInst *)(tbb);
          if (br->isConditional()) {
            FCmpInst *cond = (FCmpInst *)br->getCondition();
            unsigned opcode = cond->getOpcode();
            if (opcode == Instruction::FCmp) {
              if (cond->getPredicate() == FCmpInst::FCMP_TRUE) {
                DEBUG_WITH_TYPE("gen",
                                errs() << "bcf: an always true predicate !\n");
                toDelete.push_back(cond); // The condition
                toEdit.push_back(tbb);    // The branch using the condition
              }
            }
          }
        }
        /*
        for (BasicBlock::iterator bi = fi->begin(), be = fi->end() ; bi != be;
        ++bi){ bi->setName(""); // setting the basic blocks' names
        }
        */
      }
    }


    // Replacing all the branches we found
    for (std::vector<Instruction *>::iterator i = toEdit.begin();
         i != toEdit.end(); ++i) {
    // errs()<< *i<<"zzzzzzzz";
        // 声明 hash_function
  
    // verifyFunction(*hashFunction);
    // M.print(outs(), nullptr);



      //  IRBuilder<> Builder(*i);

      //    // 创建一个Load指令
      //  Value *opX = Builder.CreateLoad(Type::getInt32Ty(M.getContext()), x,
      //  "");

      //  // 创建一个加法指令
      //  Value *addInst = Builder.CreateAdd(opX,
      //  ConstantInt::get(Type::getInt32Ty(M.getContext()), 1), "");

      //      // 创建一个乘法指令
      //  Value *mulInst = Builder.CreateMul(opX, addInst, "");

      //   // 创建一个取模指令
      //   Value *uremInst = Builder.CreateURem(mulInst,
      //   ConstantInt::get(Type::getInt32Ty(M.getContext()), 2), "");

      //      // 将取模结果作为参数传递给哈希函数
      //   std::vector<Value *> args;
      //   args.push_back(uremInst);
      //   errs() << *i;
      //   // 创建对哈希函数的调用
      //   // Function *hashFunc = createHashFunction(M);
      //   // if (!hashFunc) {
      //   //     errs() << "Error: hash_function not found\n";
      //   //      return false;
      //   //  }
      // Function *hashFunc;
      //   CallInst *callInst = Builder.CreateCall(hashFunc, args, "");

      //       // 创建对哈希函数的第二次调用
      //   Value *zeroValue = ConstantInt::get(Type::getInt32Ty(M.getContext()),
      //   0); CallInst *callInst1 = Builder.CreateCall(hashFunc, zeroValue,
      //   "");

      //     // 创建比较指令
      //   Value *condition = Builder.CreateICmpEQ(callInst, callInst1, "");

      //     if (allocaInsts.size() != 0) {
      //       opX = new LoadInst ((Value*)allocaInsts[llvm::cryptoutils->get_uint32_t() %
      //       allocaInsts.size()], "", (*i));
      //       // opX = new LoadInst ((Value*)allocaInsts[1], "", (*i));
      //       opX->print(outs());
      //       //  opY = new LoadInst ((Value
      //       // *)allocaInsts[llvm::cryptoutils->get_uint32_t() %
      //       // allocaInsts.size()], "", (*i));
      //   // opx =
      //   //     bogusCondBuilder.CreateLoad(allocaInsts[rng() %
      //   // allocaInsts.size()]);
      // } else {
      opX = new LoadInst((Value *)x, "", (*i));
      //  opY = new LoadInst ((Value *)y, "", (*i));
      // }
      
      // //if y < 10 || x*(x+1) % 2 == 0
      // opX = new LoadInst ((Value *)x, "", (*i));
      // opY = new LoadInst ((Value *)y, "", (*i));

      op = BinaryOperator::Create(
          Instruction::Add, (Value *)opX,
          ConstantInt::get(Type::getInt32Ty(M.getContext()), 1, false), "",
          (*i));
      op1 =BinaryOperator::Create(Instruction::Mul, (Value *)opX, op, "", (*i));
      op = BinaryOperator::Create(
          Instruction::URem, op1,
          ConstantInt::get(Type::getInt32Ty(M.getContext()), 2,false),
          "", (*i));
      

      // op->print(outs());

      //      Value *C1 = ConstantInt::get(Type::getInt32Ty(M.getContext()),
      //      0xcc9e2d51);
      // Value *C2 = ConstantInt::get(Type::getInt32Ty(M.getContext()),
      // 0x1b873593);

      // // x = x * C1
      // // Value *K1 = Builder.CreateMul(X, C1, "k1");
      // op1 = BinaryOperator::Create(Instruction::Mul, C1, op, "", (*i));
      // // k1 = (k1 << 15) | (k1 >> (32 - 15))
      // // Value *K1ShiftedLeft = Builder.CreateShl(K1,
      // ConstantInt::get(Type::getInt32Ty(Context), 15), "k1_shift_left");
      // Value *K1ShiftedLeft1 = BinaryOperator::Create(Instruction::Shl, op1,
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 15), "", (*i));
      // Value *K1ShiftedRight1 = BinaryOperator::Create(Instruction::LShr, op1,
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 17), "", (*i));
      // // Value *K1ShiftedRight = Builder.CreateLShr(K1,
      // ConstantInt::get(Type::getInt32Ty(Context), 17), "k1_shift_right");
      // // K1 = Builder.CreateOr(K1ShiftedLeft, K1ShiftedRight, "k1_rotated");
      // op1 = BinaryOperator::Create(Instruction::Or, K1ShiftedLeft1,
      // K1ShiftedRight1, "", (*i));

      // // k1 = k1 * C2
      // // K1 = Builder.CreateMul(K1, C2, "k1_multiplied");
      // op1 = BinaryOperator::Create(Instruction::Mul, op1, C2, "", (*i));

      // // hash = k1
      // Value *Hash = op1;

      // // Finalization mix - force all bits of a hash block to avalanche
      // // Hash = Builder.CreateXor(Hash,
      // ConstantInt::get(Type::getInt32Ty(Context), 16), "hash_xor_16"); Hash =
      // BinaryOperator::Create(Instruction::Xor, Hash,
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 16), "", (*i));
      // // Hash = Builder.CreateMul(Hash,
      // ConstantInt::get(Type::getInt32Ty(Context), 0x85ebca6b),
      // "hash_multiplied_2"); Hash = BinaryOperator::Create(Instruction::Mul,
      // Hash, ConstantInt::get(Type::getInt32Ty(M.getContext()), 0x85ebca6b),
      // "", (*i));
      // // Hash = Builder.CreateXor(Hash,
      // ConstantInt::get(Type::getInt32Ty(Context), 13), "hash_xor_13"); Hash =
      // BinaryOperator::Create(Instruction::Xor, Hash,
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 13), "", (*i));
      // // Hash = Builder.CreateMul(Hash,
      // ConstantInt::get(Type::getInt32Ty(Context), 0xc2b2ae35),
      // "hash_multiplied_3"); Hash = BinaryOperator::Create(Instruction::Mul,
      // Hash, ConstantInt::get(Type::getInt32Ty(M.getContext()), 0xc2b2ae35),
      // "", (*i));
      // // Hash = Builder.CreateXor(Hash,
      // ConstantInt::get(Type::getInt32Ty(Context), 16), "hash_xor_16_final");
      // Hash = BinaryOperator::Create(Instruction::Xor, Hash,
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 16), "", (*i));

      // op1 = BinaryOperator::Create(Instruction::Mul, C1,
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 0), "", (*i));
      // // k1 = (k1 << 15) | (k1 >> (32 - 15))
      // // Value *K1ShiftedLeft = Builder.CreateShl(K1,
      // ConstantInt::get(Type::getInt32Ty(Context), 15), "k1_shift_left");
      // Value *K1ShiftedLeft = BinaryOperator::Create(Instruction::Shl, op1,
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 15), "", (*i));
      // Value *K1ShiftedRight = BinaryOperator::Create(Instruction::LShr, op1,
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 17), "", (*i));
      // // Value *K1ShiftedRight = Builder.CreateLShr(K1,
      // ConstantInt::get(Type::getInt32Ty(Context), 17), "k1_shift_right");
      // // K1 = Builder.CreateOr(K1ShiftedLeft, K1ShiftedRight, "k1_rotated");
      // op1 = BinaryOperator::Create(Instruction::Or, K1ShiftedLeft,
      // K1ShiftedRight, "", (*i));

      // // k1 = k1 * C2
      // // K1 = Builder.CreateMul(K1, C2, "k1_multiplied");
      // op1 = BinaryOperator::Create(Instruction::Mul, op1, C2, "", (*i));

      // // hash = k1
      // Value *Hash1 = op1;

      // // Finalization mix - force all bits of a hash block to avalanche
      // // Hash = Builder.CreateXor(Hash,
      // ConstantInt::get(Type::getInt32Ty(Context), 16), "hash_xor_16"); Hash1
      // = BinaryOperator::Create(Instruction::Xor, Hash1,
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 16), "", (*i));
      // // Hash = Builder.CreateMul(Hash,
      // ConstantInt::get(Type::getInt32Ty(Context), 0x85ebca6b),
      // "hash_multiplied_2"); Hash1 = BinaryOperator::Create(Instruction::Mul,
      // Hash1, ConstantInt::get(Type::getInt32Ty(M.getContext()), 0x85ebca6b),
      // "", (*i));
      // // Hash = Builder.CreateXor(Hash,
      // ConstantInt::get(Type::getInt32Ty(Context), 13), "hash_xor_13"); Hash1
      // = BinaryOperator::Create(Instruction::Xor, Hash1,
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 13), "", (*i));
      // // Hash = Builder.CreateMul(Hash,
      // ConstantInt::get(Type::getInt32Ty(Context), 0xc2b2ae35),
      // "hash_multiplied_3"); Hash1 = BinaryOperator::Create(Instruction::Mul,
      // Hash1, ConstantInt::get(Type::getInt32Ty(M.getContext()), 0xc2b2ae35),
      // "", (*i));
      // // Hash = Builder.CreateXor(Hash,
      // ConstantInt::get(Type::getInt32Ty(Context), 16), "hash_xor_16_final");
      // Hash1= BinaryOperator::Create(Instruction::Xor, Hash1,
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 16), "", (*i));




      Value *opres = op;


      //  Instruction *i1 = dyn_cast<Instruction>(op);
    
      // 创建调用哈希函数的指令
      // std::vector<Value *> args;
      // args.push_back(Call); // 传递一个参数给哈希函数
      // args.push_back(ConstantInt::get(Type::getInt64Ty(M.getContext()), 1, false)); // 传递一个参数给哈希函数
      // CallInst *callInst =
      //     CallInst::Create(addFunction, args, "", *i);

      // std::vector<Value *> args2;
      // args2.push_back(Call1); // 传递一个参数给哈希函数
      // args2.push_back(ConstantInt::get(Type::getInt64Ty(M.getContext()), 1, false)); // 传递一个参数给哈希函数
      // CallInst *callInst1 = CallInst::Create(
      //     addFunction,
      //     args2, "", *i);
      //     Value *callResult = callInst1;
      
      //  CallInst *callInst = new CallInst(M->getFunction("dummy_hash") opres,
      //  "", (*i));
      //   Value *HashValue = Builder.CreateCall(M->getFunction("dummy_hash"),
      //   {Input});
      //  Value *LeftOperand = op->getOperand(0);
      //  auto HashValue = hash_value(cast<ConstantInt>(opres)->getZExtValue());
      // Value *HashResult = ConstantInt::get(Type::getInt32Ty(M.getContext()),
      // static_cast<uint32_t>(HashValue)); opX= new LoadInst ((Value *)op, "",
      // (*i));
      // outs() << "Hash of the opX instruction: " << << "\n";
      //  outs() << "Value of BinaryOperator (Add): ";
      //  outs()<<HashValue;
      //  opres->print(outs());
      //  outs() << "\n";
      //  outs() << "Hash of the opX instruction: " ;
      //  outs()<<HashResult;
      //   HashResult->print(outs());
      //  outs()<<"\n";
      // opX= new LoadInst ((Value *)op, "", (*i));

      //     ShiftRight = BinaryOperator::Create(Instruction::LShr, op,
      //         ConstantInt::get(Type::getInt32Ty(M.getContext()), 1,
      //           false), "", (*i));
      //     ShiftLeft = BinaryOperator::Create(Instruction::Shl, op,
      //         ConstantInt::get(Type::getInt32Ty(M.getContext()), 1,
      //           false), "", (*i));
      //     Xor= BinaryOperator::Create(Instruction::Xor,ShiftRight,
      //     ShiftLeft,"", (*i));

      // //         Value *ShiftRight = Builder.CreateLShr(op,
      // ConstantInt::get(Type::getInt32Ty(Context), 1), "shift_right");
      // // Value *ShiftLeft = Builder.CreateShl(op,
      // ConstantInt::get(Type::getInt32Ty(Context), 1), "shift_left");
      // // Value *Xor = Builder.CreateXor(ShiftRight, ShiftLeft, "xor");
      // Value *MagicNumber = ConstantInt::get(Type::getInt32Ty(M.getContext()),
      // 0x9e3779b9); Hash=BinaryOperator::Create(Instruction::Xor,(Value *)Xor,
      // MagicNumber,"", (*i));
      // // Value *Hash = Builder.CreateAdd(Xor, MagicNumber, "hash");

      //  ShiftRight1 = BinaryOperator::Create(Instruction::LShr,
      //  ConstantInt::get(Type::getInt32Ty(M.getContext()), 0),
      //         ConstantInt::get(Type::getInt32Ty(M.getContext()), 1,
      //           false), "", (*i));
      //     ShiftLeft1 = BinaryOperator::Create(Instruction::Shl,
      //     ConstantInt::get(Type::getInt32Ty(M.getContext()), 0),
      //         ConstantInt::get(Type::getInt32Ty(M.getContext()), 1,
      //           false), "", (*i));
      //     Xor1= BinaryOperator::Create(Instruction::Xor,ShiftRight1,
      //     ShiftLeft1,"", (*i));

      // //         Value *ShiftRight = Builder.CreateLShr(op,
      // ConstantInt::get(Type::getInt32Ty(Context), 1), "shift_right");
      // // Value *ShiftLeft = Builder.CreateShl(op,
      // ConstantInt::get(Type::getInt32Ty(Context), 1), "shift_left");
      // // Value *Xor = Builder.CreateXor(ShiftRight, ShiftLeft, "xor");
      // Value *MagicNumber1 =
      // ConstantInt::get(Type::getInt32Ty(M.getContext()), 0x9e3779b9);
      // Hash1=BinaryOperator::Create(Instruction::Xor,(Value *)Xor1,
      // MagicNumber1,"", (*i));

      //  opX = new LoadInst ((Value
      //  *)ConstantInt::get(Type::getInt1Ty(M.getContext()),
      //  llvm::hash_value(opX)!=llvm::hash_value((int)0)), "", (*i)); opY1 =
      //  new LoadInst ((Value
      //  *)ConstantInt::get(Type::getInt1Ty(M.getContext()), 1), "", (*i));
      // size_t hash=hash_value(LeftOperand);
      // size_t hash1=hash_value(0);
      // outs() << "Hash of the XOR instruction: " << hash << "\n";
      //  outs() << "Hash of the 0 instruction: " << hash1 << "\n";

      // Value result=(llvm::hash_value(op)==llvm::hash_value(0))
      // condition = new ICmpInst((*i), ICmpInst::ICMP_EQ, op,
      //      ConstantInt::get(Type::getInt32Ty(M.getContext()), 0));



      //     condition = new ICmpInst((*i), ICmpInst::ICMP_EQ, (Value *)callInst,
      //  ConstantInt::get(Type::getInt64Ty(M.getContext()), 17029045464858290652,
      //    false));



      // hash obfuscation
      if(ObfType=="hash"){
            std::vector<Value*> ArgsV;
    ArgsV.push_back(opres);
    CallInst *Call = CallInst::Create(IntToStrFunc, ArgsV, "calltmp", *i);
    //  std::vector<Value*> ArgsV1;
    // ArgsV1.push_back(ConstantInt::get(Type::getInt32Ty(M.getContext()), 0, false));
    // CallInst *Call1 = CallInst::Create(IntToStrFunc, ArgsV1, "calltmp", *i);
      condition = new ICmpInst((*i), ICmpInst::ICMP_EQ, (Value *)Call,
                               ConstantInt::get(Type::getInt32Ty(M.getContext()), 1221515329, false));
      }
      // Fermat obfuscation
      if(ObfType=="fm"){
    std::vector<Value*> ArgsV;
    ArgsV.push_back(opres);
    CallInst *Call = CallInst::Create(IntToStrFunc, ArgsV, "calltmp", *i);
         condition = new ICmpInst((*i), ICmpInst::ICMP_EQ, (Value *)Call,
                               ConstantInt::get(Type::getInt32Ty(M.getContext()), 0, false));
      }
      // Fibonacci obfuscation
      if(ObfType=="fib"){
             std::vector<Value*> ArgsV2;
    ArgsV2.push_back(ConstantInt::get(Type::getInt32Ty(M.getContext()), FibNum, false));
    CallInst *Call2 = CallInst::Create(IntToStrFunc, ArgsV2, "calltmp", *i);

      std::vector<Value*> ArgsV3;
    ArgsV3.push_back(ConstantInt::get(Type::getInt32Ty(M.getContext()), FibNum-1, false));
    CallInst *Call3 = CallInst::Create(IntToStrFunc, ArgsV3, "calltmp", *i);

          std::vector<Value*> ArgsV4;
    ArgsV4.push_back(ConstantInt::get(Type::getInt32Ty(M.getContext()), FibNum-2, false));
    CallInst *Call4 = CallInst::Create(IntToStrFunc, ArgsV4, "calltmp", *i);
    BinaryOperator *callAdd = BinaryOperator::Create(
          Instruction::Add, (Value *)Call3,
          (Value *)Call4, "",
          (*i));
         condition = new ICmpInst((*i), ICmpInst::ICMP_EQ, (Value *)Call2,
                               (Value *)callAdd);
      }

      // O-LLVM default obfuscation
      if(ObfType=="default"){
              condition = new ICmpInst((*i), ICmpInst::ICMP_EQ, op,
           ConstantInt::get(Type::getInt32Ty(M.getContext()), 0));
      //       condition2 = new ICmpInst(
      //     (*i), ICmpInst::ICMP_SLT, (Value *)opY,
      //     ConstantInt::get(Type::getInt32Ty(M.getContext()), 10, false));
      // op1 = BinaryOperator::Create(Instruction::Or, (Value *)condition,
      //                              (Value *)condition2, "", (*i));
      //  condition=(Value *)op1;
      }
//  condition = new ICmpInst((*i), ICmpInst::ICMP_EQ, (Value *)callInst,
//                                ConstantInt::get(Type::getInt32Ty(M.getContext()), 1, false));

      // condition2 = new ICmpInst(
      //     (*i), ICmpInst::ICMP_SLT, opY,
      //     ConstantInt::get(Type::getInt32Ty(M.getContext()), 10, false));

 

      BranchInst::Create(((BranchInst *)*i)->getSuccessor(0),
                         ((BranchInst *)*i)->getSuccessor(1),
                         (Value *)condition, ((BranchInst *)*i)->getParent());
      DEBUG_WITH_TYPE("gen", errs() << "bcf: Erase branch instruction:"
                                    << *((BranchInst *)*i) << "\n");
      (*i)->eraseFromParent(); // erase the branch
    }
    // Erase all the associated conditions we found
    for (std::vector<Instruction *>::iterator i = toDelete.begin();
         i != toDelete.end(); ++i) {
      DEBUG_WITH_TYPE("gen", errs() << "bcf: Erase condition instruction:"
                                    << *((Instruction *)*i) << "\n");
      (*i)->eraseFromParent();
    }

    // Only for debug
    DEBUG_WITH_TYPE("cfg", errs() << "bcf: End of the pass, here are the "
                                     "graphs after doFinalization\n");
    for (Module::iterator mi = M.begin(), me = M.end(); mi != me; ++mi) {
      DEBUG_WITH_TYPE("cfg", errs()
                                 << "bcf: Function " << mi->getName() << "\n");
      DEBUG_WITH_TYPE("cfg", mi->viewCFG());
    }

    return true;
  } // end of doFinalization
}; // end of struct BogusControlFlow : public FunctionPass
} // namespace
// extern "C" uint32_t hash_function(uint32_t input) {
//     // unsigned char hash[SHA256_DIGEST_LENGTH];
//     // SHA256_CTX sha256;

//     // SHA256_Init(&sha256);
//     // SHA256_Update(&sha256, &input, sizeof(input));
//     // SHA256_Final(hash, &sha256);

//     // // 仅取前4个字节作为示例
//     // uint32_t result;
//     // memcpy(&result, hash, sizeof(result));
//     uint32_t result;
//     result=input+20;
//     return result;
// }
char BogusControlFlow::ID = 0;
static RegisterPass<BogusControlFlow> X("boguscf",
                                        "inserting bogus control flow");

Pass *llvm::createBogus() { return new BogusControlFlow(); }

Pass *llvm::createBogus(bool flag) { return new BogusControlFlow(flag); }
