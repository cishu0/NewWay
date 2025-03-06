#include "llvm/Transforms/Obfuscation/VariableRotation.h"
#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CFG.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
//#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/Cloning.h"
//#include "llvm/Transforms/IPO/PassManagerBuilder.h"
#include "llvm/Transforms/Utils/Local.h" 
#include <stdio.h>
#include "assert.h"
#include <vector>
#include <algorithm>
#include <ctime>
#include <cstdlib>
#include <cstdio>
#include <string>

using namespace llvm;
using namespace std;

namespace
{
    struct VariableRotation : public ModulePass
    {
        static char ID;
        bool flag;
 
        VariableRotation() : ModulePass(ID) {}
        VariableRotation(bool flag) : ModulePass(ID) { this->flag = flag; }

        Function *Rotate(Module *m,PointerType *ptrType,Twine &name);
        bool toObfuscate(bool flag, Function* f, std::string attribute);
        string readAnnotate(Function* f);
        bool valueEscapes(Instruction* Inst);
        void doFunc(Function &f,SetVector<Function*> &shift);
        bool doVar(Function &f,SetVector<AllocaInst*> &vars,Function *rotateFunc);
        bool isUsedByInst(Instruction *inst,Value *var)
        {
            for(Value *ops:inst->operands())
                if(ops==var)
                    return true;
            return false;
        }

 
        bool runOnModule(Module &m)
        {
            Twine fname1=Twine("vrFunc");
            //shiftFunc为变换函数
            Function *shiftFunc=Rotate(&m,Type::getInt8PtrTy(m.getContext()),fname1);
            SetVector<Function*> shifts;
            //将变换函数添加到shifts
            shifts.insert(shiftFunc);
            for(Function &f:m)
            {
                //函数是构造的轮转函数则跳过
                if(&f==shiftFunc)
                    continue;

                //函数有完整定义
                if (f.hasExactDefinition()) {
                    if (toObfuscate(flag, &f, "vrobf")) {
                        doFunc(f, shifts);
                    }
                }
            }
            return true;
        }
      };
}
 
char VariableRotation::ID=0;
static RegisterPass<VariableRotation> X("vrobf", "Call vrobf", false, false);
Pass *llvm::createVariableRotation() {return new VariableRotation();}
Pass *llvm::createVariableRotation(bool flag) {return new VariableRotation(flag);}

bool VariableRotation::toObfuscate(bool flag, Function* f, string attribute) {
    string attr = attribute;
    string attrNo = "no" + attr;

    //函数是声明而非检测
    if (f->isDeclaration()) {
        return false;
    }

    //函数具有外部可见的链接属性，则可能在其他地方定义，不适合在当前上下文混淆
    if (f->hasAvailableExternallyLinkage() != 0) {
        return false;
    }

    //如果注解中存在novrobf，//@novrobf
    if (readAnnotate(f).find(attrNo) != std::string::npos) {
        return false;
    }

    //如果注解中存在vrobf，//@vrobf
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
string VariableRotation::readAnnotate(Function* f) {
    std::string annotation = "";

    // Get annotation variable
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

bool VariableRotation::valueEscapes(Instruction* Inst) {
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

//对函数内的变量进行变量轮转
bool VariableRotation::doVar(Function &f,SetVector<AllocaInst*> &vars,Function *rotate)
{
    //指令数就俩，没必要
    if(vars.size()<2)
        return false;

    //向函数头部插入指令
    IRBuilder<> irb(&*f.getEntryBlock().getFirstInsertionPt());
    //创建一个0
    Value *zero=ConstantInt::get(irb.getInt32Ty(),0);
    //获取模块中的数据类型等
    DataLayout data=f.getParent()->getDataLayout();
    int space=0;

    SetVector<int> value_map;
    printf("function: %s\n",f.getName());

    //将每个变量的应有偏移位置写入映射表
    for(int i=0;i<vars.size();i++)
    {
        AllocaInst *a=vars[i];
        //将偏移地址入表
        value_map.insert(space);
        printf("address:  %d\n",space);
        space+=data.getTypeAllocSize(a->getAllocatedType());
    }

    //定义长为space的元素大小8位的数组
    ArrayType *arrayType=ArrayType::get(irb.getInt8Ty(),space);
    //栈上分配数组类型的空间，作为轮转空间
    AllocaInst *array=irb.CreateAlloca(arrayType);
    int prob=30;

    //初始化array，将vars列表中的变量复制到array中
    for (int i = 0; i < vars.size(); i++) {
        AllocaInst* var = vars[i];
        int index = value_map[i];
        Value* gep = irb.CreateGEP(array, { zero, ConstantInt::get(irb.getInt32Ty(), index) });
        Value* cast = irb.CreateBitOrPointerCast(gep, var->getAllocatedType()->getPointerTo());
        irb.CreateStore(irb.CreateLoad(var), cast);
    }

    //对基本块上的指令进行迭代，修改变量为偏移地址
    for(BasicBlock &bb:f)
    {
        int offset=0;
        //插入点迭代器
        BasicBlock::iterator iter=bb.getFirstInsertionPt();
        //函数进入块则跳过，入口块是参数初始化和栈帧设置，不应被修改或添加
        if(&bb==&f.getEntryBlock())
            iter++;
        while(iter!=bb.end())
        {
            Instruction *inst=&*iter;
            //inst为插入点
            irb.SetInsertPoint(inst);

            for(int i=0;i<vars.size();i++)
                //该指令是否使用了某一个变量
                if(isUsedByInst(inst,vars[i]))
                {
                    //60%概率进行变量替换
                    if(rand()%100<prob)
                    {
                        //随机次数
                        int times=rand()%(vars.size()-1)+1;
                        //计算变量现应移动多少距离，不使用times，防止数组访问越界
                        int delta=(space+value_map[(offset+times)%vars.size()]-value_map[offset])%space;
                        //对轮转空间进行距离次轮转
                        irb.CreateCall(rotate,{irb.CreateGEP(array,{zero,zero}),
                                ConstantInt::get(irb.getInt32Ty(),space),
                                ConstantInt::get(irb.getInt32Ty(),delta)});
                        //轮转之后，计算现在变量指针的相对偏移量
                        offset=(offset+times)%vars.size();
                    }
                    //计算现在的索引
                    int index=(space+value_map[i]-value_map[offset])%space;
                    //访问该变量，取出并规范类型，寻找指令中的对应变量，将原引用修改为偏移地址形式
                    Value *gep=irb.CreateGEP(array,{zero,ConstantInt::get(irb.getInt32Ty(),index)});
                    Value *cast=irb.CreateBitOrPointerCast(gep,vars[i]->getType());
                    int c=0;
                    //对当前指令的所有操作数进行遍历，如为刚计算出偏移地址的变量，对其进行更换
                    for(Value *ops:inst->operands())
                    {
                        if(ops==vars[i])
                            inst->setOperand(c,cast);
                        c++;
                    }
                    break;
                }
            iter++;
        }
        //进入下一个函数前，将偏移保持为0
        if(offset!=0)
        {
            irb.SetInsertPoint(bb.getTerminator());
            irb.CreateCall(rotate,{irb.CreateGEP(array,{zero,zero}),ConstantInt::get(irb.getInt32Ty(),space),ConstantInt::get(irb.getInt32Ty(),(space-value_map[offset])%space)});
        }
 
    }
    return true;
}

//对函数执行变量轮转
void VariableRotation::doFunc(Function &f,SetVector<Function*> &shift)
{
    //list收集变量指针
    SetVector<AllocaInst*> list;
    for(BasicBlock &bb:f)
        for(Instruction &instr:bb)
            if(isa<AllocaInst>(instr))
            {
                AllocaInst *a=(AllocaInst*)&instr;
                // 检查是否为char数组，如果是则跳过
                if (a->getAllocatedType()->isArrayTy() &&
                    a->getAllocatedType()->getArrayElementType()->isIntegerTy(8)) {
                    continue;
                }
                list.insert(a);
            }
    //对收集的变量进行处理，shift[0]是轮转函数
    if(doVar(f,list,shift[0]))
    {
        for(AllocaInst *a:list)
            a->eraseFromParent();
    }
}

//生成用于旋转变量的函数，执行一次能旋转一位
Function *VariableRotation::Rotate(Module *m,PointerType *ptrType,Twine &name)
{
    //构建参数列表
    std::vector<Type*> params;
    params.push_back(ptrType);
    params.push_back(Type::getInt32Ty(m->getContext()));
    params.push_back(Type::getInt32Ty(m->getContext()));
    //格式
    Type *rawType=ptrType->getPointerElementType();
    //创建私有非可变参数函数
    FunctionType *funcType=FunctionType::get(Type::getVoidTy(m->getContext()),params,false);
    Function *func=Function::Create(funcType,GlobalValue::PrivateLinkage,name,m);

    //在函数中创建一系列基本块
    BasicBlock *entry1=BasicBlock::Create(m->getContext(),"entry1",func);
    BasicBlock *cmp1=BasicBlock::Create(m->getContext(),"cmp1",func);
    BasicBlock *entry2=BasicBlock::Create(m->getContext(),"entry2",func);
    BasicBlock *cmp2=BasicBlock::Create(m->getContext(),"cmp2",func);
    BasicBlock *shift=BasicBlock::Create(m->getContext(),"shift",func);
    BasicBlock *end2=BasicBlock::Create(m->getContext(),"end2",func);
    BasicBlock *end1=BasicBlock::Create(m->getContext(),"end1",func);
    //iter获取函数参数
    Function::arg_iterator iter=func->arg_begin();
    //依次取出函数的参数，模块地址，长度、？
    Value *ptr=&*iter;
    Value *len=&*++iter;
    Value *times=&*++iter;

    //对entry1构建IR指令，指针为irb
    IRBuilder<> irb(entry1);
    //创建了两个常数
    Value *zero=ConstantInt::get(irb.getInt32Ty(),0);
    Value *one=ConstantInt::get(irb.getInt32Ty(),1);
    //分配相应类型栈空间，生成变量
    AllocaInst *i=irb.CreateAlloca(irb.getInt32Ty());
    AllocaInst *j=irb.CreateAlloca(irb.getInt32Ty());
    AllocaInst *tmp=irb.CreateAlloca(rawType);
    AllocaInst *array=irb.CreateAlloca(ptrType);
    //对变量j赋值zero
    irb.CreateStore(zero,j);
    irb.CreateStore(ptr,array);
    //创建到cmp1的无条件跳转
    irb.CreateBr(cmp1);

    //设置irb在cmp1末尾插入点
    irb.SetInsertPoint(cmp1);
    //j<times,就跳转到entry2，否则跳转到end1
    irb.CreateCondBr(irb.CreateICmpSLT(irb.CreateLoad(j),times),entry2,end1);
 
    //设置irb在cmp2插入
    irb.SetInsertPoint(entry2);
    //对变量赋值
    irb.CreateStore(zero,i);
    //对变量tmp赋array[0]
    irb.CreateStore(irb.CreateLoad(irb.CreateInBoundsGEP(irb.CreateLoad(array),{zero})),tmp);
    irb.CreateBr(cmp2);
 
    //设置对cmp2的处理
    irb.SetInsertPoint(cmp2);
    //i<len-1，就shift，否则end2
    irb.CreateCondBr(irb.CreateICmpSLT(irb.CreateLoad(i),irb.CreateSub(len,one)),shift,end2);
 
    //设置对shift的处理
    irb.SetInsertPoint(shift);
    Value *ival=irb.CreateLoad(i);
    Value *arr=irb.CreateLoad(array);
    //存储arr[ival+1]到arr[ival]，irb.CreateInBoundsGEP(arr,{irb.CreateAdd(ival,one)})起始地址＋偏移
    irb.CreateStore(irb.CreateLoad(irb.CreateInBoundsGEP(arr,{irb.CreateAdd(ival,one)})),irb.CreateInBoundsGEP(rawType,arr,{ival}));
    //i=ival+1
    irb.CreateStore(irb.CreateAdd(ival,one),i);
    irb.CreateBr(cmp2);
 
    //编写end2
    irb.SetInsertPoint(end2);
    //j=j+1
    irb.CreateStore(irb.CreateAdd(irb.CreateLoad(j),one),j);
    //array[len-1]=tmp
    irb.CreateStore(irb.CreateLoad(tmp),irb.CreateInBoundsGEP(irb.CreateLoad(array),{irb.CreateSub(len,one)}));
    irb.CreateBr(cmp1);
    
    //end1返回块
    irb.SetInsertPoint(end1);
    irb.CreateRetVoid();
    return func;
}
