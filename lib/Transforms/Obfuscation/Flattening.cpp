#include "llvm/Transforms/Obfuscation/Flattening.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/CryptoUtils.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Transforms/Utils/Local.h"
#include <time.h>
#include <stdlib.h>
#include <stdio.h>
#include <sstream>


#define DEBUG_TYPE "flattening"

using namespace std;
using namespace llvm;

//统计被扁平化的函数数目
STATISTIC(Flattened, "Functions flattened");

//本pass中所需
namespace {
    struct Flattening : public FunctionPass {
        static char ID;
        bool flag;

        Flattening() : FunctionPass(ID) {}
        Flattening(bool flag) : FunctionPass(ID) { this->flag = flag; }

        bool runOnFunction(Function& F);
        bool toObfuscate(bool flag, Function* f, std::string attribute);
        bool flatten(Function* f);
        string readAnnotate(Function* f);
        bool valueEscapes(Instruction* Inst);
    };
}

//pass管理器读取id地址而非变量值
char Flattening::ID = 0;
//注册该pass到LLVMpass中，属于pass规范，用户可使用参数1调用
static RegisterPass<Flattening> X("flattening", "Call graph flattening");
//该pass的开关，根据bool值决定是否启用
Pass* llvm::createFlattening(bool flag) { return new Flattening(flag); }

//因为LLVM在pass执行时，会逐个传入函数并运行执行函数，所有执行控制流平坦化的对象选择为函数
bool Flattening::runOnFunction(Function& F) {
    Function* tmp = &F;
    //如果函数符合flatten混淆条件
    if (toObfuscate(flag, tmp, "fla")) {
        if (flatten(tmp)) {
            ++Flattened;
        }
    }

    return false;
}

//toObfuscate实现
bool Flattening::toObfuscate(bool flag, Function* f, std::string attribute) {
    std::string attr = attribute;
    std::string attrNo = "no" + attr;

    //函数是声明而非检测
    if (f->isDeclaration()) {
        return false;
    }

    //函数具有外部可见的链接属性，则可能在其他地方定义，不适合在当前上下文混淆
    if (f->hasAvailableExternallyLinkage() != 0) {
        return false;
    }

    //如果注解中存在nofla，//@nofla
    if (readAnnotate(f).find(attrNo) != std::string::npos) {
        return false;
    }

    //如果注解中存在fla，//@fla
    if (readAnnotate(f).find(attr) != std::string::npos) {
        return true;
    }

    //命令行标志有设置
    if (flag == true) {
        return true;
    }

    return false;
}

//读取注解
string Flattening::readAnnotate(Function* f) {
    std::string annotation = "";

    GlobalVariable* glob =
        f->getParent()->getGlobalVariable("llvm.global.annotations");

    if (glob != NULL) {

        if (ConstantArray* ca = dyn_cast<ConstantArray>(glob->getInitializer())) {
            for (unsigned i = 0; i < ca->getNumOperands(); ++i) {

                if (ConstantStruct* structAn =
                    dyn_cast<ConstantStruct>(ca->getOperand(i))) {
                    if (ConstantExpr* expr =
                        dyn_cast<ConstantExpr>(structAn->getOperand(0))) {

                        if (expr->getOpcode() == Instruction::BitCast &&
                            expr->getOperand(0) == f) {
                            ConstantExpr* note = cast<ConstantExpr>(structAn->getOperand(1));

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

bool Flattening::valueEscapes(Instruction* Inst) {
    BasicBlock* BB = Inst->getParent();
    for (Value::use_iterator UI = Inst->use_begin(), E = Inst->use_end(); UI != E;
        ++UI) {
        Instruction* I = cast<Instruction>(*UI);
        if (I->getParent() != BB || isa<PHINode>(I)) {
            return true;
        }
    }
    return false;
}


//flattening主体功能实现
bool Flattening::flatten(Function* f) {
    //所需基本块变量
    vector<BasicBlock*> origBB;
    BasicBlock* flaEntry;
    BasicBlock* flaEnd;
    BasicBlock* flaEnd2;

    LoadInst* entry;
    LoadInst* end;
    LoadInst* end2;
    SwitchInst* switchI;
    SwitchInst* switchI2;
    SwitchInst* switchI3;
    AllocaInst* switchVar;

    //0-1随机数
    srand((unsigned int)time(NULL));
    int ret = rand() % 2;

    //加密所需密钥
    char scrambling_key[16];
    llvm::cryptoutils->get_bytes(scrambling_key, 16);

    //对函数中的switch语句降级为if，对其进行控制流混淆
    FunctionPass* lower = createLowerSwitchPass();
    lower->runOnFunction(*f);

    //遍历f，对从头到尾的所有基本块进行检查，加入容器
    for (Function::iterator i = f->begin(); i != f->end(); ++i) {
        BasicBlock* tmp = &*i;
        origBB.push_back(tmp);

        //检查该基本块是否依靠异常处理进行终止
        BasicBlock* bb = &*i;
        if (isa<InvokeInst>(bb->getTerminator())) {
            return false;
        }
    }

    //基本块小于等于1，函数不适合进行控制流平坦化
    if (origBB.size() <= 1) {
        return false;
    }

    //从origBB中删除第一个基本块
    origBB.erase(origBB.begin());

    //获取函数中第一个基本块
    Function::iterator tmp = f->begin();  //++tmp;
    BasicBlock* insert = &*tmp;

    //函数第一个基本块是否以条件语句结束，是则赋值给br，使用强制类型转换
    BranchInst* br = NULL;
    if (isa<BranchInst>(insert->getTerminator())) {
        br = cast<BranchInst>(insert->getTerminator());
    }

    //如果函数的第一个基本块终止指令为有条件分支指令（即 br 不为空并且是条件分支）
    //或者具有多个后继基本块
    if ((br != NULL && br->isConditional()) ||
        insert->getTerminator()->getNumSuccessors() > 1) {
        //end指向最后一条语句之后
        BasicBlock::iterator i = insert->end();
        --i;
        //指向倒数第二条语句
        if (insert->size() > 1) {
            --i;
        }

        //拆分第一个基本块，tmpBB为i之前，first为i及之后
        BasicBlock* tmpBB = insert->splitBasicBlock(i, "first");
        origBB.insert(origBB.begin(), tmpBB);
    }

    //移除第一基本块内的跳转指令
    insert->getTerminator()->eraseFromParent();

    //在第一基本块处创建并初始化 switchVar 变量，通过在栈帧上分配局部变量实现
    switchVar =
        new AllocaInst(Type::getInt32Ty(f->getContext()), 0, "switchVar", insert);
    //对switchVar加密赋值
    new StoreInst(
        ConstantInt::get(Type::getInt32Ty(f->getContext()),
            llvm::cryptoutils->scramble32(0, scrambling_key)),
        switchVar, insert);

    // 创建主要跳转功能依赖基本块
    flaEntry = BasicBlock::Create(f->getContext(), "loopEntry", f, insert);
    flaEnd = BasicBlock::Create(f->getContext(), "loopEnd", f, insert);
    flaEnd2 = BasicBlock::Create(f->getContext(), "loopEnd2", f, insert);

    //在循环入口块中读取switchVar 变量值（如此也能有switch的流程）
    entry = new LoadInst(switchVar, "switchVar", flaEntry);

    //在循环出口块中读取 switchVar 变量（实现真正的跳转）
    end = new LoadInst(switchVar, "switchVar", flaEnd);

    //在循环出口块中读取 switchVar 变量（实现真正的跳转）
    end2 = new LoadInst(switchVar, "switchVar", flaEnd2);

    //将第一块基本块移到顶端，创建第一块到入口块的无条件跳转
    insert->moveBefore(flaEntry);
    BranchInst::Create(flaEntry, insert);

    //默认分支块放到loopend之前，并无条件跳转至loopend
    BasicBlock* swDefault =
        BasicBlock::Create(f->getContext(), "switchDefault", f, flaEnd);
    BranchInst::Create(flaEnd, swDefault);

    // 创建switch选择开关，放在loopentry内，并设置跳转逻辑依赖，switchVar作为条件值
    switchI = SwitchInst::Create(entry, swDefault, 0, flaEntry);

    // 创建switch选择开关，放在loopend内，并设置跳转逻辑依赖，switchVar作为条件值
    switchI2 = SwitchInst::Create(end, swDefault, 0, flaEnd);

    // 创建switch选择开关，放在loopend2内，并设置跳转逻辑依赖，switchVar作为条件值
    switchI3 = SwitchInst::Create(end2, swDefault, 0, flaEnd2);

    //从函数的第一个基本块中移除分支跳转指令，并设置一个新的跳转指令，使得控制流跳转到主循环的入口点
    f->begin()->getTerminator()->eraseFromParent();

    BranchInst::Create(flaEntry, &*f->begin());

    //将所有基本块赋case值
    for (vector<BasicBlock*>::iterator b = origBB.begin(); b != origBB.end();
        ++b) {
        BasicBlock* i = *b;
        ConstantInt* numCase = NULL;

        //每一块都在loopend之前
        i->moveBefore(flaEnd);

        //据跳转分支的所需数据类型，获取numcase
        numCase = cast<ConstantInt>(ConstantInt::get(
            switchI->getCondition()->getType(),
            llvm::cryptoutils->scramble32(switchI->getNumCases(), scrambling_key)));
        //设置跳转分支in与条件值numcase
        switchI->addCase(numCase, i);
        switchI2->addCase(numCase, i);
        switchI3->addCase(numCase, i);
    }

    //补全分割后的，不在原函数基本块遍历序列中的基本块的case值
    for (vector<BasicBlock*>::iterator b = origBB.begin(); b != origBB.end();
        ++b) {
        BasicBlock* i = *b;
        ConstantInt* numCase = NULL;

        //如为返回块则跳过
        if (i->getTerminator()->getNumSuccessors() == 0) {
            continue;
        }

        // 如果现基本块是非条件跳转
        if (i->getTerminator()->getNumSuccessors() == 1) {
            //获取后继基本块，删除当前基本块的跳转指令
            BasicBlock* succ = i->getTerminator()->getSuccessor(0);
            i->getTerminator()->eraseFromParent();

            //获取后继基本块的case值
            numCase = switchI->findCaseDest(succ);

            //如果后续块没有case值,赋case
            if (numCase == NULL) {
                numCase = cast<ConstantInt>(
                    ConstantInt::get(switchI->getCondition()->getType(),
                        llvm::cryptoutils->scramble32(
                            switchI->getNumCases() - 1, scrambling_key)));
            }

            //使用下一基本块numcase更新switchVar，并将此赋值语句写入i
            new StoreInst(numCase, entry->getPointerOperand(), i);

            //建立默认值后续块与其numcase的在switch开关中的对应
            switchI->addCase(numCase, succ);
            switchI2->addCase(numCase, succ);
            switchI3->addCase(numCase, succ);

            //随机跳转looped块
            ret = rand() % 2;
            if (ret == 0) {
                BranchInst::Create(flaEnd, i);
                continue;
            }
            else
            {
                BranchInst::Create(flaEnd2, i);
                continue;
            }
        }

        //如为两个后继的if跳转
        if (i->getTerminator()->getNumSuccessors() == 2) {

            //获取后续基本块的跳转对应数值
            ConstantInt* numCaseTrue =
                switchI->findCaseDest(i->getTerminator()->getSuccessor(0));
            ConstantInt* numCaseFalse =
                switchI->findCaseDest(i->getTerminator()->getSuccessor(1));

            //如果无case值，则为其生成跳转条件值
            if (numCaseTrue == NULL) {
                numCaseTrue = cast<ConstantInt>(
                    ConstantInt::get(switchI->getCondition()->getType(),
                        llvm::cryptoutils->scramble32(
                            switchI->getNumCases() - 1, scrambling_key)));
            }

            if (numCaseFalse == NULL) {
                numCaseFalse = cast<ConstantInt>(
                    ConstantInt::get(switchI->getCondition()->getType(),
                        llvm::cryptoutils->scramble32(
                            switchI->getNumCases() - 1, scrambling_key)));
            }

            //创建指令，存放将终止的类if跳转指令修改为类switch指令，creat在最终指令前创建分支指令
            BranchInst* br = cast<BranchInst>(i->getTerminator());
            SelectInst* sel =
                SelectInst::Create(br->getCondition(), numCaseTrue, numCaseFalse, "",
                    i->getTerminator());

            //删除原终止指令
            i->getTerminator()->eraseFromParent();

            //使用下一应执行基本块的case值更新switchVar，并将此赋值语句写入i
            new StoreInst(sel, entry->getPointerOperand(), i);

            //随机跳转looped块
            ret = rand() % 2;
            if (ret == 0) {
                BranchInst::Create(flaEnd, i);
                continue;
            }
            else
            {
                BranchInst::Create(flaEnd2, i);
                continue;
            }
        }
    }

    //修复Phi、reg节点，防止其被影响
    std::vector<PHINode*> tmpPhi;
    std::vector<Instruction*> tmpReg;
    BasicBlock* bbEntry = &*f->begin();

    do {
        tmpPhi.clear();
        tmpReg.clear();

        for (Function::iterator i = f->begin(); i != f->end(); ++i) {

            for (BasicBlock::iterator j = i->begin(); j != i->end(); ++j) {

                if (isa<PHINode>(j)) {
                    PHINode* phi = cast<PHINode>(j);
                    tmpPhi.push_back(phi);
                    continue;
                }
                if (!(isa<AllocaInst>(j) && j->getParent() == bbEntry) &&
                    (valueEscapes(&*j) || j->isUsedOutsideOfBlock(&*i))) {
                    tmpReg.push_back(&*j);
                    continue;
                }
            }
        }
        for (unsigned int i = 0; i != tmpReg.size(); ++i) {
            DemoteRegToStack(*tmpReg.at(i), f->begin()->getTerminator());
        }

        for (unsigned int i = 0; i != tmpPhi.size(); ++i) {
            DemotePHIToStack(tmpPhi.at(i), f->begin()->getTerminator());
        }

    } while (tmpReg.size() != 0 || tmpPhi.size() != 0);

    return true;
}
