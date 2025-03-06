#include "llvm/Transforms/Obfuscation/BogusControlFlow.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/Local.h" 
#include <stdio.h>

// 定义统计用宏
#define DEBUG_TYPE "BogusControlFlow"
STATISTIC(NumFunction, "a. Number of functions in this module");
STATISTIC(NumTimesOnFunctions, "b. Number of times we run on each function");
STATISTIC(InitNumBasicBlocks, "c. Initial number of basic blocks in this module");
STATISTIC(NumModifiedBasicBlocks, "d. Number of modified basic blocks");
STATISTIC(NumAddedBasicBlocks, "e. Number of added basic blocks in this module");
STATISTIC(FinalNumBasicBlocks, "f. Final number of basic blocks in this module");
//调试宏，opt对应操作，gen对应完成，cfg对应控制流图

using namespace std;
using namespace llvm;

// pass命令行选项
const int defaultObfRate = 60, defaultObfTime = 1;

//函数混淆概率
static cl::opt<int>
ObfProbRate("bcf_prob", 
    cl::desc("Choose the probability [%] each basic blocks will be obfuscated by the -bcf pass"),
    cl::value_desc("probability rate"), cl::init(defaultObfRate), cl::Optional);

//函数混淆次数
static cl::opt<int>
ObfTimes("bcf_loop",
    cl::desc("Choose how many time the -bcf pass loop on a function"), 
    cl::value_desc("number of times"), cl::init(defaultObfTime), cl::Optional);

namespace {
    struct BogusControlFlow : public FunctionPass {
        //pass定义所需
        static char ID;
        bool flag;
        BogusControlFlow() : FunctionPass(ID) {}
        BogusControlFlow(bool flag) : FunctionPass(ID) { this->flag = flag; BogusControlFlow(); }

        //混淆入口
        virtual bool runOnFunction(Function& F) {
            //保障混淆次数正确
            if (ObfTimes <= 0) {
                errs() << "BogusControlFlow application number -bcf_loop=x must be x > 0";
                return false;
            }

            //保障混淆概率正确
            if (!((ObfProbRate > 0) && (ObfProbRate <= 100))) {
                errs() << "BogusControlFlow application basic blocks percentage -bcf_prob=x must be 0 < x <= 100";
                return false;
            }
            //如果能够进行bfc混淆，执行混淆主体函数
            if (toObfuscate(flag, &F, "bcf")) {
                bogus(F);
                doF(*F.getParent());
                return true;
            }

            return false;
        }

        bool toObfuscate(bool flag, Function* f, std::string attribute) {
            std::string attr = attribute;
            std::string attrNo = "no" + attr;

            // Check if declaration
            if (f->isDeclaration()) {
                return false;
            }

            // Check external linkage
            if (f->hasAvailableExternallyLinkage() != 0) {
                return false;
            }

            //不处理异常终止块
            for (Function::iterator i = f->begin(); i != f->end(); ++i) {
                BasicBlock* bb = &*i;
                if (isa<InvokeInst>(bb->getTerminator())) {
                    return false;
                }
            }

  
            if (readAnnotate(f).find(attrNo) != std::string::npos) {
                return false;
            }


            if (readAnnotate(f).find(attr) != std::string::npos) {
                return true;
            }

            if (flag == true) {
                return true;
            }

            return false;
        }

        //注解读取
        string readAnnotate(Function* f) {
            string annotation = "";
            GlobalVariable* glob =
                f->getParent()->getGlobalVariable("llvm.global.annotations");

            //全局变量非空
            if (glob != NULL) {
                //遍历数组
                if (ConstantArray* ca = dyn_cast<ConstantArray>(glob->getInitializer())) {
                    for (unsigned i = 0; i < ca->getNumOperands(); ++i) {
                        //获取结构体
                        if (ConstantStruct* structAn =
                            dyn_cast<ConstantStruct>(ca->getOperand(i))) {
                            if (ConstantExpr* expr =
                                dyn_cast<ConstantExpr>(structAn->getOperand(0))) {
                                //注解是否和当前函数有关
                                if (expr->getOpcode() == Instruction::BitCast &&
                                    expr->getOperand(0) == f) {
                                    ConstantExpr* note = cast<ConstantExpr>(structAn->getOperand(1));
                                    // 找到注解并构建所有注解到一个字符串
                                    if (note->getOpcode() == Instruction::GetElementPtr) {
                                        if (GlobalVariable* annoteStr =
                                            dyn_cast<GlobalVariable>(note->getOperand(0))) {
                                            if (ConstantDataSequential* data =
                                                dyn_cast<ConstantDataSequential>(
                                                    annoteStr->getInitializer())) {
                                                if (data->isString()) {
                                                    annotation += data->getAsString().lower() + " ";
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            return annotation;
        }

        //整个函数每一块添加虚假控制流的判断与加入
        void bogus(Function& F) {
 
            ++NumFunction;
            int NumBasicBlocks = 0;

            bool firstTime = true; 

            bool hasBeenModified = false;
           
            //传入的指定混淆概率超限，设为默认概率
            if (ObfProbRate < 0 || ObfProbRate > 100) {
                ObfProbRate = defaultObfRate;
            }
            //传入的指定混淆次数超限，设为默认次数
            if (ObfTimes <= 0) {
                ObfTimes = defaultObfTime;
            }
            //修改宏与混淆次数变量
            NumTimesOnFunctions = ObfTimes;
            int NumObfTimes = ObfTimes;

            //在函数上循环指定次数次
            do {
                
                //收集本函数所有基本块到列表中
                std::list<BasicBlock*> basicBlocks;
                for (Function::iterator i = F.begin(); i != F.end(); ++i) {
                    basicBlocks.push_back(&*i);
                }

                //基本块不为空
                while (!basicBlocks.empty()) {
                    NumBasicBlocks++;
                    //概率性选择选择基本块
                    if ((int)llvm::cryptoutils->get_range(100) <= ObfProbRate) {
                        
                        hasBeenModified = true;
                        ++NumModifiedBasicBlocks;
                        NumAddedBasicBlocks += 3;
                        FinalNumBasicBlocks += 3;
                        //向给定的第一个基本块加入虚假控制流
                        BasicBlock* basicBlock = basicBlocks.front();
                        //随机选择真实块在真/假
                        switch (llvm::cryptoutils->get_range(2)) {
                        case 0:
                            addFalsebf(basicBlock, F);
                            break;
                        case 1:
                            addTruebf(basicBlock, F);
                            break;
                        }
                    }
                   
                    //该基本块混淆结束，从列表移除
                    basicBlocks.pop_front();

                    //首次迭代此函数
                    if (firstTime) {
                        ++InitNumBasicBlocks;
                        ++FinalNumBasicBlocks;
                    }
                }
               
                //标志已非首次处理此函数
                firstTime = false;
            } while (--NumObfTimes > 0);
        }

        //形成原块在真分支的虚假控制流
        virtual void addTruebf(BasicBlock* basicBlock, Function& F) {
            //拆分基本块，使第一部分只含phi节点和splitBasicBlock创建的调试信息与终止符
            //第二部分含原块的所有指令
            //如此处理，无需调整所有phi、元数据等
            //必须使phi节点在第一部分，因为实际在第二部分据它们进行了更新

            //迭代器放在传入基本块伊始
            BasicBlock::iterator i1 = basicBlock->begin();
            //如果基本块有第一个非PHI、非调试信息指令、非生命周期管理指令的指令，将此指令给基本块迭代器
            if (basicBlock->getFirstNonPHIOrDbgOrLifetime())
                i1 = (BasicBlock::iterator)basicBlock->getFirstNonPHIOrDbgOrLifetime();
            
            //用twine接受originalBB传给基本块分割函数，分割后，originalBB指向第2块
            Twine* var;
            var = new Twine("originalBB");
            BasicBlock* originalBB = basicBlock->splitBasicBlock(i1, *var);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: First and original basic blocks: ok\n");

            //为第一块的跳转添加一块修改过的基本块
            Twine* var3 = new Twine("alteredBB");
            BasicBlock* alteredBB = getAlter(originalBB, *var3, &F);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Altered basic block: ok\n");

            //所有基本块创建完毕，修改终止命令，以调整控制流
            alteredBB->getTerminator()->eraseFromParent();
            basicBlock->getTerminator()->eraseFromParent();
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator removed from the altered"
                << " and first basic blocks\n");

            //准备一个分支命令，使结果始终为真
            //在此完成in doFinalization()
            Value* LHS = ConstantFP::get(Type::getFloatTy(F.getContext()), 1.0);
            Value* RHS = ConstantFP::get(Type::getFloatTy(F.getContext()), 1.0);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Value LHS and RHS created\n");

            //第一块的尾部，创建恒真的分支
            Twine* var4 = new Twine("condition");
            FCmpInst* condition = new FCmpInst(*basicBlock, FCmpInst::FCMP_TRUE, LHS, RHS, *var4);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Always true condition created\n");

            //跳转到为真的原始基本块，改后的基本块始终为假
            BranchInst::Create(originalBB, alteredBB, (Value*)condition, basicBlock);
            DEBUG_WITH_TYPE("gen",
                errs() << "bcf: Terminator instruction in first basic block: ok\n");

            //改后基本块运行结束回到原块，false在此循环
            BranchInst::Create(originalBB, alteredBB);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator instruction in altered block: ok\n");
            //originalBB被修改为有时返回值，有时继续循环，当然，实则永远为真，因为终止符不变，但也可能被混淆

            //originalBB终止指令前迭代器
            BasicBlock::iterator i = originalBB->end();

            //分割，只需要第二部分的终止指令
            Twine* var5 = new Twine("originalBBpart2");
            BasicBlock* originalBBpart2 = originalBB->splitBasicBlock(--i, *var5);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator part of the original basic block"
                << " is isolated\n");
            //修改块的第一部分是返回指令或开始，于是我们应该在分割时删除此指令的创建
            originalBB->getTerminator()->eraseFromParent();
            //在最后加入一个常为真/假的分支
            Twine* var6 = new Twine("condition2");
            switch (llvm::cryptoutils->get_range(2)) {
            case 0:{//恒假跳转
                FCmpInst * condition2 = new FCmpInst(*originalBB, CmpInst::FCMP_FALSE, LHS, RHS, *var6);
                BranchInst::Create(alteredBB, originalBBpart2, (Value*)condition2, originalBB);
                DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator original basic block: ok\n");
                DEBUG_WITH_TYPE("gen", errs() << "bcf: End of addBogusFlow().\n");
                break;
                }
            case 1:{//恒真跳转
                FCmpInst* condition2 = new FCmpInst(*originalBB, CmpInst::FCMP_TRUE, LHS, RHS, *var6);
                BranchInst::Create(originalBBpart2, alteredBB, (Value*)condition2, originalBB);
                DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator original basic block: ok\n");
                DEBUG_WITH_TYPE("gen", errs() << "bcf: End of addBogusFlow().\n");
                break;
                }
            }
        }

        //形成原块在假分支的虚假控制流
        virtual void addFalsebf(BasicBlock* basicBlock, Function& F) {
            //拆分基本块，使第一部分只含phi节点和splitBasicBlock创建的调试信息与终止符
            //第二部分含原块的所有指令
            //如此处理，无需调整所有phi、元数据等
            //必须使phi节点在第一部分，因为实际在第二部分据它们进行了更新

            //迭代器放在传入基本块伊始
            BasicBlock::iterator i1 = basicBlock->begin();
            //如果基本块有第一个非PHI、非调试信息指令、非生命周期管理指令的指令，将此指令给基本块迭代器
            if (basicBlock->getFirstNonPHIOrDbgOrLifetime())
                i1 = (BasicBlock::iterator)basicBlock->getFirstNonPHIOrDbgOrLifetime();

            //用twine接受originalBB传给基本块分割函数，分割后，originalBB指向
            Twine* var;
            var = new Twine("originalBB");
            BasicBlock* originalBB = basicBlock->splitBasicBlock(i1, *var);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: First and original basic blocks: ok\n");

            //为第一块的跳转添加一块修改过的基本块
            Twine* var3 = new Twine("alteredBB");
            BasicBlock* alteredBB = getAlter(originalBB, *var3, &F);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Altered basic block: ok\n");

            //所有基本块创建完毕，删除块间链接，修改终止命令，以调整控制流
            alteredBB->getTerminator()->eraseFromParent();
            basicBlock->getTerminator()->eraseFromParent();
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator removed from the altered"
                << " and first basic blocks\n");

            //准备一个分支命令，使结果始终为假
            Value* LHS = ConstantFP::get(Type::getFloatTy(F.getContext()), 1.0);
            Value* RHS = ConstantFP::get(Type::getFloatTy(F.getContext()), 1.0);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Value LHS and RHS created\n");

            //第一块之后，恒假的分支
            Twine* var4 = new Twine("condition");
            FCmpInst* condition = new FCmpInst(*basicBlock, FCmpInst::FCMP_FALSE, LHS, RHS, *var4);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Always false condition created\n");

            //分支判断结果为恒假，故真实块放在假分支
            BranchInst::Create(alteredBB, originalBB, (Value*)condition, basicBlock);
            DEBUG_WITH_TYPE("gen",
                errs() << "bcf: Terminator instruction in first basic block: ok\n");

            //改后基本块运行结束回到原块，True在此循环
            BranchInst::Create(originalBB, alteredBB);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator instruction in altered block: ok\n");
            //originalBB被修改为有时返回值，有时继续循环，当然，实则永远为真，因为终止符不变，但也可能被混淆

            //originalBB终止指令前迭代指令
            BasicBlock::iterator i = originalBB->end();

            //分割，只需要第二部分的终止指令
            Twine* var5 = new Twine("originalBBpart2");
            BasicBlock* originalBBpart2 = originalBB->splitBasicBlock(--i, *var5);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator part of the original basic block"
                << " is isolated\n");

            //修改块的第一部分是返回指令或开始，于是我们应该在分割时删除此指令的创建
            originalBB->getTerminator()->eraseFromParent();

            //随机建立恒假/恒真分支语句，将结束块放在恒假/恒真分支中
            Twine* var6 = new Twine("condition2");
            switch (llvm::cryptoutils->get_range(2)) {
            case 0: {//恒假跳转
                FCmpInst* condition2 = new FCmpInst(*originalBB, CmpInst::FCMP_FALSE, LHS, RHS, *var6);
                BranchInst::Create(alteredBB, originalBBpart2, (Value*)condition2, originalBB);
                DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator original basic block: ok\n");
                DEBUG_WITH_TYPE("gen", errs() << "bcf: End of addBogusFlow().\n");
                break;
                }
            case 1: {//恒真跳转
                FCmpInst* condition2 = new FCmpInst(*originalBB, CmpInst::FCMP_TRUE, LHS, RHS, *var6);
                BranchInst::Create(originalBBpart2, alteredBB, (Value*)condition2, originalBB);
                DEBUG_WITH_TYPE("gen", errs() << "bcf: Terminator original basic block: ok\n");
                DEBUG_WITH_TYPE("gen", errs() << "bcf: End of addBogusFlow().\n");
                break;
                }
            }
        }

        //创建虚拟块
        virtual BasicBlock* getAlter(BasicBlock* basicBlock,
            const Twine& Name = "gen", Function* F = 0) {
            //对重新映射相关指令信息有用
            ValueToValueMapTy VMap;
            BasicBlock* alteredBB = llvm::CloneBasicBlock(basicBlock, VMap, Name, F);
            DEBUG_WITH_TYPE("gen", errs() << "bcf: Original basic block cloned\n");
            //将PHI节点等进行修改
            BasicBlock::iterator ji = basicBlock->begin();
            for (BasicBlock::iterator i = alteredBB->begin(), e = alteredBB->end(); i != e; ++i) {
                //指令操作数上循环
                for (User::op_iterator opi = i->op_begin(), ope = i->op_end(); opi != ope; ++opi) {
                    //对操作数进行映射，使用新块中的引用值。防止当前各类变化影响到真实块的数据
                    Value* v = MapValue(*opi, VMap, RF_None, 0);
                    if (v != 0) {
                        *opi = v;
                    }
                }
  
                //重新映射phi节点的传入块
                if (PHINode* pn = dyn_cast<PHINode>(i)) {
                    for (unsigned j = 0, e = pn->getNumIncomingValues(); j != e; ++j) {
                        Value* v = MapValue(pn->getIncomingBlock(j), VMap, RF_None, 0);
                        if (v != 0) {
                            pn->setIncomingBlock(j, cast<BasicBlock>(v));
                        }
                    }
                }
                DEBUG_WITH_TYPE("gen", errs() << "bcf: PHINodes remapped\n");
                //重新映射附加的元数据为本块
                SmallVector<std::pair<unsigned, MDNode*>, 4> MDs;
                i->getAllMetadata(MDs);
                DEBUG_WITH_TYPE("gen", errs() << "bcf: Metadatas remapped\n");
                i->setDebugLoc(ji->getDebugLoc());
                ji++;
            }


            // 在块的中间添加随机指令
            for (BasicBlock::iterator i = alteredBB->begin(), e = alteredBB->end(); i != e; ++i) {
                // 如果我们找到二元运算符，通过随机插入一些指令来轻微修改这部分
                if (i->isBinaryOp()) { // 二元指令
                    unsigned opcode = i->getOpcode();
                    BinaryOperator* op, * op1 = NULL;
                    Twine* var = new Twine("_");
                    // 对浮点数和整数分别处理
                    // 二元整数
                    if (opcode == Instruction::Add || opcode == Instruction::Sub ||
                        opcode == Instruction::Mul || opcode == Instruction::UDiv ||
                        opcode == Instruction::SDiv || opcode == Instruction::URem ||
                        opcode == Instruction::SRem || opcode == Instruction::Shl ||
                        opcode == Instruction::LShr || opcode == Instruction::AShr ||
                        opcode == Instruction::And || opcode == Instruction::Or ||
                        opcode == Instruction::Xor) {
                        for (int random = (int)llvm::cryptoutils->get_range(10); random < 10; ++random) {
                            switch (llvm::cryptoutils->get_range(4)) { 
                            case 0: // 什么都不做
                                break;
                            case 1: op = BinaryOperator::CreateNeg(i->getOperand(0), *var, &*i);
                                op1 = BinaryOperator::Create(Instruction::Add, op,
                                    i->getOperand(1), "gen", &*i);
                                break;
                            case 2: op1 = BinaryOperator::Create(Instruction::Sub,
                                i->getOperand(0),
                                i->getOperand(1), *var, &*i);
                                op = BinaryOperator::Create(Instruction::Mul, op1,
                                    i->getOperand(1), "gen", &*i);
                                break;
                            case 3: op = BinaryOperator::Create(Instruction::Shl,
                                i->getOperand(0),
                                i->getOperand(1), *var, &*i);
                                break;
                            }
                        }
                    }
                    // 二元浮点数
                    if (opcode == Instruction::FAdd || opcode == Instruction::FSub ||
                        opcode == Instruction::FMul || opcode == Instruction::FDiv ||
                        opcode == Instruction::FRem) {
                        for (int random = (int)llvm::cryptoutils->get_range(10); random < 10; ++random) {
                            switch (llvm::cryptoutils->get_range(3)) { 
                            case 0: // 什么都不做
                                break;
                            case 1: op = BinaryOperator::CreateFNeg(i->getOperand(0), *var, &*i);
                                op1 = BinaryOperator::Create(Instruction::FAdd, op,
                                    i->getOperand(1), "gen", &*i);
                                break;
                            case 2: op = BinaryOperator::Create(Instruction::FSub,
                                    i->getOperand(0),
                                    i->getOperand(1), *var, &*i);
                                op1 = BinaryOperator::Create(Instruction::FMul, op,
                                    i->getOperand(1), "gen", &*i);
                                break;
                            }
                        }
                    }
                    if (opcode == Instruction::ICmp) { // 条件 (整数)
                        ICmpInst* currentI = (ICmpInst*)(&i);
                        switch (llvm::cryptoutils->get_range(3)) { 
                        case 0: // 什么都不做
                            break;
                        case 1: currentI->swapOperands();
                            break;
                        case 2: // 随机改变谓词
                            switch (llvm::cryptoutils->get_range(10)) {
                            case 0: currentI->setPredicate(ICmpInst::ICMP_EQ);
                                break; // 相等
                            case 1: currentI->setPredicate(ICmpInst::ICMP_NE);
                                break; // 不相等
                            case 2: currentI->setPredicate(ICmpInst::ICMP_UGT);
                                break; // 无符号大于
                            case 3: currentI->setPredicate(ICmpInst::ICMP_UGE);
                                break; // 无符号大于等于
                            case 4: currentI->setPredicate(ICmpInst::ICMP_ULT);
                                break; // 无符号小于
                            case 5: currentI->setPredicate(ICmpInst::ICMP_ULE);
                                break; // 无符号小于等于
                            case 6: currentI->setPredicate(ICmpInst::ICMP_SGT);
                                break; // 有符号大于
                            case 7: currentI->setPredicate(ICmpInst::ICMP_SGE);
                                break; // 有符号大于等于
                            case 8: currentI->setPredicate(ICmpInst::ICMP_SLT);
                                break; // 有符号小于
                            case 9: currentI->setPredicate(ICmpInst::ICMP_SLE);
                                break; // 有符号小于等于
                            }
                            break;
                        }

                    }
                    if (opcode == Instruction::FCmp) { // 条件 (浮点数)
                        FCmpInst* currentI = (FCmpInst*)(&i);
                        switch (llvm::cryptoutils->get_range(3)) { // 需要改进
                        case 0: // 什么都不做
                            break;
                        case 1: currentI->swapOperands();
                            break;
                        case 2: // 随机改变谓词
                            switch (llvm::cryptoutils->get_range(10)) {
                            case 0: currentI->setPredicate(FCmpInst::FCMP_OEQ);
                                break; // 有序且相等
                            case 1: currentI->setPredicate(FCmpInst::FCMP_ONE);
                                break; // 有序且操作数不等
                            case 2: currentI->setPredicate(FCmpInst::FCMP_UGT);
                                break; // 无序或大于
                            case 3: currentI->setPredicate(FCmpInst::FCMP_UGE);
                                break; // 无序或大于等于
                            case 4: currentI->setPredicate(FCmpInst::FCMP_ULT);
                                break; // 无序或小于
                            case 5: currentI->setPredicate(FCmpInst::FCMP_ULE);
                                break; // 无序或小于等于
                            case 6: currentI->setPredicate(FCmpInst::FCMP_OGT);
                                break; // 有序且大于
                            case 7: currentI->setPredicate(FCmpInst::FCMP_OGE);
                                break; // 有序且大于等于
                            case 8: currentI->setPredicate(FCmpInst::FCMP_OLT);
                                break; // 有序且小于
                            case 9: currentI->setPredicate(FCmpInst::FCMP_OLE);
                                break; // 有序或小于等于
                            }
                            break;
                        }
                    }
                }
            }
            return alteredBB;
        }


        /* doFinalization
         * 重写 FunctionPass 方法以对整个模块应用转换。
         * 使用恒真/恒假不透明谓词替换原有恒真/恒假谓词
         * 它还将移除所有函数的基本块和指令的名称。
         */
        bool doF(Module& M) {

            //声明两个全局变量：x 和 y，并用数学表达式不透明谓词替换 FCMP_TRUE/FCMP_FALSE 谓词
            Twine* varX = new Twine("x");
            Twine* varY = new Twine("y");
            Value* x1 = ConstantInt::get(Type::getInt32Ty(M.getContext()), 0, false);
            Value* y1 = ConstantInt::get(Type::getInt32Ty(M.getContext()), 0, false);

            GlobalVariable* x = new GlobalVariable(M, Type::getInt32Ty(M.getContext()), false,
                GlobalValue::CommonLinkage, (Constant*)x1,
                *varX);
            GlobalVariable* y = new GlobalVariable(M, Type::getInt32Ty(M.getContext()), false,
                GlobalValue::CommonLinkage, (Constant*)y1,
                *varY);

            std::vector<Instruction*> toTEdit, toDelete, toFEdit;
            BinaryOperator* op, * op1 = NULL;
            LoadInst* opX, * opY;
            ICmpInst* condition, * condition2;

            // 寻找需要转换的条件和分支
            for (Module::iterator mi = M.begin(), me = M.end(); mi != me; ++mi) {
                for (Function::iterator fi = mi->begin(), fe = mi->end(); fi != fe; ++fi) {
                    TerminatorInst* tbb = fi->getTerminator();

                    if (tbb->getOpcode() == Instruction::Br) {
                        BranchInst* br = (BranchInst*)(tbb);

                        if (br->isConditional()) {
                            FCmpInst* cond = (FCmpInst*)br->getCondition();
                            unsigned opcode = cond->getOpcode();

                            if (opcode == Instruction::FCmp) {

                                //对含有恒真谓词的放入容器处理
                                if (cond->getPredicate() == FCmpInst::FCMP_TRUE) {

                                    DEBUG_WITH_TYPE("gen",
                                        errs() << "bcf: 永真谓词！\n");
                                    toDelete.push_back(cond); // 条件
                                    toTEdit.push_back(tbb);    // 使用恒真条件的分支
                                }
                                //对含有恒假谓词的放入容器处理
                                else if (cond->getPredicate() == FCmpInst::FCMP_FALSE) {

                                    DEBUG_WITH_TYPE("gen",
                                        errs() << "bcf: 永假谓词！\n");
                                    toDelete.push_back(cond); // 条件
                                    toFEdit.push_back(tbb);    // 使用使用恒假条件的分支
                                }
                            }
                        }
                    }
                }
            }

            // 处理找到的所有恒真式子
            for (std::vector<Instruction*>::iterator i = toTEdit.begin(); i != toTEdit.end(); ++i) {
                //随机选择一种恒真不透明谓词替换方式
                switch (llvm::cryptoutils->get_range(2)) {
                case 0:
                    //if y < 10 || x * (x + 1) % 2 == 0
                    opX = new LoadInst((Value*)x, "", (*i));
                    opY = new LoadInst((Value*)y, "", (*i));

                    op = BinaryOperator::Create(Instruction::Add, (Value*)opX,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 1,
                            false), "", (*i));
                    op1 = BinaryOperator::Create(Instruction::Mul, (Value*)opX, op, "", (*i));
                    op = BinaryOperator::Create(Instruction::URem, op1,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 2,
                            false), "", (*i));
                    condition = new ICmpInst((*i), ICmpInst::ICMP_EQ, op,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 0,
                            false));
                    condition2 = new ICmpInst((*i), ICmpInst::ICMP_SLT, opY,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 10,
                            false));
                    op1 = BinaryOperator::Create(Instruction::Or, (Value*)condition,
                        (Value*)condition2, "", (*i));

                    BranchInst::Create(((BranchInst*)*i)->getSuccessor(0),
                        ((BranchInst*)*i)->getSuccessor(1), (Value*)op1,
                        ((BranchInst*)*i)->getParent());
                    break;
                case 1:
                    //if x > 10 || x * x + y * y >= 0
                    opX = new LoadInst((Value*)x, "", (*i));
                    opY = new LoadInst((Value*)y, "", (*i));

                    op = BinaryOperator::Create(Instruction::Mul, (Value*)opX, (Value*)opX, "", (*i));
                    op1 = BinaryOperator::Create(Instruction::Mul, (Value*)opY, (Value*)opY, "", (*i));
                    op = BinaryOperator::Create(Instruction::Add, op, op1, "", (*i));
                    condition = new ICmpInst((*i), ICmpInst::ICMP_SGE, op,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 0,
                            false));
                    condition2 = new ICmpInst((*i), ICmpInst::ICMP_SGT, opX,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 10,
                            false));
                    op1 = BinaryOperator::Create(Instruction::Or, (Value*)condition,
                        (Value*)condition2, "", (*i));

                    BranchInst::Create(((BranchInst*)*i)->getSuccessor(0),
                        ((BranchInst*)*i)->getSuccessor(1), (Value*)op1,
                        ((BranchInst*)*i)->getParent());
                    break;
                }
                //删除原分支指令
                DEBUG_WITH_TYPE("gen", errs() << "bcf: 删除分支指令:" << *((BranchInst*)*i) << "\n");
                (*i)->eraseFromParent(); //从原基本块中删除该分支指令
            }

            // 处理找到的所有恒假式子
            for (std::vector<Instruction*>::iterator i = toFEdit.begin(); i != toFEdit.end(); ++i) {
                //随机选择一种恒假不透明谓词替换方式
                switch (llvm::cryptoutils->get_range(2)) {
                case 0:
                    //if y < 10 && x * (x + 1) % 2 ！ = 0
                    opX = new LoadInst((Value*)x, "", (*i));
                    opY = new LoadInst((Value*)y, "", (*i));

                    op = BinaryOperator::Create(Instruction::Add, (Value*)opX,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 1,
                            false), "", (*i));
                    op1 = BinaryOperator::Create(Instruction::Mul, (Value*)opX, op, "", (*i));
                    op = BinaryOperator::Create(Instruction::URem, op1,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 2,
                            false), "", (*i));
                    condition = new ICmpInst((*i), ICmpInst::ICMP_NE, op,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 0,
                            false));
                    condition2 = new ICmpInst((*i), ICmpInst::ICMP_SLT, opY,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 10,
                            false));
                    op1 = BinaryOperator::Create(Instruction::And, (Value*)condition,
                        (Value*)condition2, "", (*i));

                    BranchInst::Create(((BranchInst*)*i)->getSuccessor(0),
                        ((BranchInst*)*i)->getSuccessor(1), (Value*)op1,
                        ((BranchInst*)*i)->getParent());
                    break;
                case 1:
                    // if x > 10 && x * x + y * y < 0
                    opX = new LoadInst((Value*)x, "", (*i));
                    opY = new LoadInst((Value*)y, "", (*i));

                    op = BinaryOperator::Create(Instruction::Mul, (Value*)opX, (Value*)opX, "", (*i));
                    op1 = BinaryOperator::Create(Instruction::Mul, (Value*)opY, (Value*)opY, "", (*i));
                    op = BinaryOperator::Create(Instruction::Add, op, op1, "", (*i));
                    condition = new ICmpInst((*i), ICmpInst::ICMP_SLT, op,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 0,
                            false));
                    condition2 = new ICmpInst((*i), ICmpInst::ICMP_SGT, opX,
                        ConstantInt::get(Type::getInt32Ty(M.getContext()), 10,
                            false));
                    op1 = BinaryOperator::Create(Instruction::And, (Value*)condition,
                        (Value*)condition2, "", (*i));

                    BranchInst::Create(((BranchInst*)*i)->getSuccessor(0),
                        ((BranchInst*)*i)->getSuccessor(1), (Value*)op1,
                        ((BranchInst*)*i)->getParent());
                    break;
                }
                //删除原分支指令
                DEBUG_WITH_TYPE("gen", errs() << "bcf: 删除分支指令:" << *((BranchInst*)*i) << "\n");
                (*i)->eraseFromParent(); //从原基本块中删除该分支指令
            }

            // 从分支语句所属基本块中，删去该条件语句
            for (std::vector<Instruction*>::iterator i = toDelete.begin(); i != toDelete.end(); ++i) {
                DEBUG_WITH_TYPE("gen", errs() << "bcf: 删除条件指令:"
                    << *((Instruction*)*i) << "\n");
                (*i)->eraseFromParent();
            }

            return true;
        } // doFinalization 结束
    };
}

char BogusControlFlow::ID = 0;
static RegisterPass<BogusControlFlow> X("boguscf", "inserting bogus control flow");

Pass* llvm::createBogus() {
    return new BogusControlFlow();
}

Pass* llvm::createBogus(bool flag) {
    return new BogusControlFlow(flag);
}
