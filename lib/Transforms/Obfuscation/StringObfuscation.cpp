#define DEBUG_TYPE "objdiv"
#include <string>
#include <sstream>

#include "llvm/ADT/Statistic.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/CryptoUtils.h"
#include "llvm/Transforms/Obfuscation/StringObfuscation.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/ModuleUtils.h"

using namespace llvm;

STATISTIC(GlobalsEncoded, "Counts number of global variables encoded");

namespace llvm {

    //加密所需数据结构，密钥长8位
    struct encVar {
    public:
        GlobalVariable* var;
        uint8_t key;
    };

    class StringObfuscationPass : public llvm::ModulePass {
    public:
        static char ID; // pass identification
        bool is_flag = false;
        StringObfuscationPass() : ModulePass(ID) {}
        StringObfuscationPass(bool flag) : ModulePass(ID)
        {
            is_flag = flag;
        }

        //防止直接被调用
        virtual bool runOnModule(Module& M) {
            if (!is_flag)
                return false;

            //需删除的全局变量和已加密的全局变量记录
            std::vector<GlobalVariable*> toDelConstGlob;
            std::vector<encVar*> encGlob;

            //收集全局变量
            for (Module::global_iterator gi = M.global_begin(), ge = M.global_end();
                gi != ge; ++gi) {
                GlobalVariable* gv = &(*gi);
                std::string::size_type str_idx = gv->getName().str().find(".str.");
                std::string section(gv->getSection());

                // 加密静态的字符串
                //寻找名称以.str开始的、有初始器的、是常量的、初始器是连续的数据序列的，所属段**
                if (gv->getName().str().substr(0, 4) == ".str" &&
                    gv->isConstant() &&
                    gv->hasInitializer() &&
                    isa<ConstantDataSequential>(gv->getInitializer()) &&
                    section != "llvm.metadata" &&
                    section.find("__objc_methname") == std::string::npos
                    ) {
                    //记录加密个数
                    ++GlobalsEncoded;

                    //新建全局变量dynGV，属性相同，但为变量
                    GlobalVariable* dynGV = new GlobalVariable(M,
                        gv->getType()->getElementType(),
                        !(gv->isConstant()), gv->getLinkage(),
                        (Constant*)0, gv->getName(),
                        (GlobalVariable*)0,
                        gv->getThreadLocalMode(),
                        gv->getType()->getAddressSpace());
                    //设置为相同初始化器，即赋相同值
                    dynGV->setInitializer(gv->getInitializer());

                    //全局变量名称获取
                    std::string tmp = gv->getName().str();

                    //检查初始化器是否为连续的数据序列，如字符串或数组，只处理连续数据序列
                    Constant* initializer = gv->getInitializer();
                    ConstantDataSequential* cdata = dyn_cast<ConstantDataSequential>(initializer);
                    //如果是连续数据序列
                    if (cdata) {

                        //原始数据获取
                        const char* orig = cdata->getRawDataValues().data();
                        unsigned len = cdata->getNumElements() * cdata->getElementByteSize();

                        //创建加密所需，变量指向新建全局变量，随机key
                        encVar* cur = new encVar();
                        cur->var = dynGV;
                        cur->key = llvm::cryptoutils->get_uint8_t();
                        
                        //使用指针修改原数据
                        char* encr = const_cast<char*>(orig);
                        //异或加密
                        for (unsigned i = 0; i != len; ++i) {
                            encr[i] = orig[i] ^ cur->key;
                        }

                        //设置初始化器，用于下一个变量收集
                        dynGV->setInitializer(initializer);

                        //放入收集已经加密的全局变量的容器
                        encGlob.push_back(cur);
                    }

                    //否则使用原初始器，不改变其值
                    else {
                        dynGV->setInitializer(initializer);
                    }

                    //使用dynGV替换gv
                    gv->replaceAllUsesWith(dynGV);
                    //gv放入待删除全局变量列表
                    toDelConstGlob.push_back(gv);

                }
            }

            //删除原有全局变量
            for (unsigned i = 0, e = toDelConstGlob.size(); i != e; ++i)
                toDelConstGlob[i]->eraseFromParent();
            //解密
            decFunc(&M, &encGlob);


            return true;
        }

    private:
        //解密函数，对模块内加密了的全局变量进行解密
        void decFunc(Module* mod, std::vector<encVar*>* gvars) {

            //参数类型容器
            std::vector<Type*>FuncTy_args;
            //函数格式
            FunctionType* FuncTy = FunctionType::get( Type::getVoidTy(mod->getContext()), FuncTy_args,false);

            uint64_t randFuncName = cryptoutils->get_uint64_t();
            std::string  random_str;
            std::stringstream random_stream;
            random_stream << randFuncName;
            random_stream >> random_str;
            randFuncName++;
            //模块中创建随机名称解密函数，遵守C调用约定
            Constant* c = mod->getOrInsertFunction(".datadiv_decode" + random_str, FuncTy);
            Function* fdecode = cast<Function>(c);
            fdecode->setCallingConv(CallingConv::C);

            //进入块创建
            BasicBlock* entry = BasicBlock::Create(mod->getContext(), "entry", fdecode);
            //在模块中创建指令插入器，指定插入点为entry块
            IRBuilder<> builder(mod->getContext());
            builder.SetInsertPoint(entry);

            //解码大体构建
            for (unsigned i = 0, e = gvars->size(); i != e; ++i) {
                
                //从加密变量的容器取出全局变量的指针和密钥
                GlobalVariable* gvar = (*gvars)[i]->var;
                uint8_t key = (*gvars)[i]->key;

                //获取初始值，用于赋值
                Constant* init = gvar->getInitializer();
                //取出常量数据序列
                ConstantDataSequential* cdata = dyn_cast<ConstantDataSequential>(init);

                //计算序列长度
                unsigned len = cdata->getNumElements() * cdata->getElementByteSize();
                --len;

                //获取插入点所在基本块
                BasicBlock* preHeaderBB = builder.GetInsertBlock();
                //向解码函数中，添加主体解码基本块和结束基本块
                BasicBlock* for_body = BasicBlock::Create(mod->getContext(), "for-body", fdecode);
                BasicBlock* for_end = BasicBlock::Create(mod->getContext(), "for-end", fdecode);
                
                //从进入块，即初始化块，跳转至主体块
                builder.CreateBr(for_body);

                //构建主体块
                builder.SetInsertPoint(for_body);
                //构建PHI节点，用于循环的使用
                PHINode* variable = builder.CreatePHI(Type::getInt32Ty(mod->getContext()), 2, "i");
                //构建循环初始条件与结束条件
                Value* startValue = builder.getInt32(0);
                Value* endValue = builder.getInt32(len);
                
                //使PHI节点为初始值
                variable->addIncoming(startValue, preHeaderBB);

                //索引构建，规定有0和variable
                Value* indexList[2] = { ConstantInt::get(variable->getType(), 0), variable };

                //获取密钥值，并建立了密钥数值到解码函数
                Value* const_key = builder.getInt8(key);
                //构建GEP，用于获取偏移，使用索引值variable进行指向数组中元素
                Value* GEP = builder.CreateGEP(gvar, ArrayRef<Value*>(indexList, 2), "arrayIdx");
                //使用GEP加载数据到函数内
                LoadInst* loadElement = builder.CreateLoad(GEP, false);
                //指针字节对齐
                loadElement->setAlignment(1);

                //创建异或
                Value* Xor = builder.CreateXor(loadElement, const_key, "xor");
                //解码结果写回
                StoreInst* Store = builder.CreateStore(Xor, GEP, false);
                //设置对齐
                Store->setAlignment(1);

                //创建1，variable+1
                Value* stepValue = builder.getInt32(1);
                Value* nextValue = builder.CreateAdd(variable, stepValue, "next-value");
                //结束条件创建，variable是否小于endValue，小于为1
                Value* endCondition = builder.CreateICmpULT(variable, endValue, "end-condition");
                //不等于为1，等于为0
                endCondition = builder.CreateICmpNE(endCondition, builder.getInt1(0), "loop-condition");
                //在循环结束块设置插入
                BasicBlock* loopEndBB = builder.GetInsertBlock();
                //如果条件为1，则跳转回loopend，否则跳转至结束块
                builder.CreateCondBr(endCondition, loopEndBB, for_end);
                //对结束块进行插入
                builder.SetInsertPoint(for_end);
                //对PHI赋值为下一个值
                variable->addIncoming(nextValue, loopEndBB);

            }
            
            //创建返回块
            builder.CreateRetVoid();
            //加入全局构造函数
            appendToGlobalCtors(*mod, fdecode, 0);


        }

    };

}

char StringObfuscationPass::ID = 0;
static RegisterPass<StringObfuscationPass> X("GVDiv", "Global variable (i.e., const char*) diversification pass", false, true);

Pass* llvm::createStringObfuscation(bool flag) {
    return new StringObfuscationPass(flag);
}
