#include "llvm/Transforms/Obfuscation/Substitution.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Obfuscation/Utils.h"
#include "llvm/IR/Intrinsics.h"

#define DEBUG_TYPE "substitution"

#define NUMBER_ADD_SUBST 5
#define NUMBER_SUB_SUBST 4
#define NUMBER_MUL_SUBST 2
//#define NUMBER_DIV_SUBST 4
#define NUMBER_AND_SUBST 2
#define NUMBER_OR_SUBST 2
#define NUMBER_XOR_SUBST 2
#define NUMBER_SHL_SUBST 2

//pass运行次数
static cl::opt<int>
ObfTimes("sub_loop",
    cl::desc("Choose how many time the -sub pass loops on a function"),
    cl::value_desc("number of times"), cl::init(1), cl::Optional);


//统计用宏
STATISTIC(Add, "Add substitued");
STATISTIC(Sub, "Sub substitued");
STATISTIC(Mul,  "Mul substitued");
STATISTIC(And, "And substitued");
STATISTIC(Or, "Or substitued");
STATISTIC(Xor, "Xor substitued");
STATISTIC(Shl,  "Shl substitued");

namespace {

    struct Substitution : public FunctionPass {
        static char ID;
        void (Substitution::* funcAdd[NUMBER_ADD_SUBST])(BinaryOperator* bo);
        void (Substitution::* funcSub[NUMBER_SUB_SUBST])(BinaryOperator* bo);
        void (Substitution::* funcMul[NUMBER_MUL_SUBST])(BinaryOperator* bo);
        void (Substitution::* funcAnd[NUMBER_AND_SUBST])(BinaryOperator* bo);
        void (Substitution::* funcOr[NUMBER_OR_SUBST])(BinaryOperator* bo);
        void (Substitution::* funcXor[NUMBER_XOR_SUBST])(BinaryOperator* bo);
        void (Substitution::* funcShl[NUMBER_SHL_SUBST])(BinaryOperator* bo);

        bool flag;

        Substitution() : FunctionPass(ID) {}

        Substitution(bool flag) : FunctionPass(ID) {
            this->flag = flag;
            funcAdd[0] = &Substitution::addNeg;
            funcAdd[1] = &Substitution::addDoubleNeg;
            funcAdd[2] = &Substitution::addRand;
            funcAdd[3] = &Substitution::addRand2;
            funcAdd[4] = &Substitution::addRand3;

            funcSub[0] = &Substitution::subNeg;
            funcSub[1] = &Substitution::subDoubleNeg;
            funcSub[2] = &Substitution::subRand;
            funcSub[3] = &Substitution::subRand2;

            funcMul[0] = &Substitution::Mul1;
            funcMul[1] = &Substitution::Mul2;

            funcAnd[0] = &Substitution::andSubstitution;
            funcAnd[1] = &Substitution::andSubstitutionRand;

            funcOr[0] = &Substitution::orSubstitution;
            funcOr[1] = &Substitution::orSubstitutionRand;

            funcXor[0] = &Substitution::xorSubstitution;
            funcXor[1] = &Substitution::xorSubstitutionRand;

            funcShl[0] = &Substitution::Shl1;
            funcShl[1] = &Substitution::Shl2;
        }

        bool runOnFunction(Function& F);
        bool change(Function* f);

        void addNeg(BinaryOperator* bo);
        void addDoubleNeg(BinaryOperator* bo);
        void addRand(BinaryOperator* bo);
        void addRand2(BinaryOperator* bo);
        void addRand3(BinaryOperator* bo);

        void subNeg(BinaryOperator* bo);
        void subDoubleNeg(BinaryOperator* bo);
        void subRand(BinaryOperator* bo);
        void subRand2(BinaryOperator* bo);

        void Mul1(BinaryOperator* bo);
        void Mul2(BinaryOperator* bo);

        void andSubstitution(BinaryOperator* bo);
        void andSubstitutionRand(BinaryOperator* bo);

        void orSubstitution(BinaryOperator* bo);
        void orSubstitutionRand(BinaryOperator* bo);

        void xorSubstitution(BinaryOperator* bo);
        void xorSubstitutionRand(BinaryOperator* bo);

        void Shl1(BinaryOperator* bo);
        void Shl2(BinaryOperator* bo);
    };
}

char Substitution::ID = 0;
static RegisterPass<Substitution> X("substitution", "operators substitution");
Pass* llvm::createSubstitution(bool flag) { return new Substitution(flag); }

bool Substitution::runOnFunction(Function& F) {
    //检查运行次数是否正确
    if (ObfTimes <= 0) {
        errs() << "Substitution application number -sub_loop=x must be x > 0";
        return false;
    }

    Function* tmp = &F;
    //混淆方式
    if (toObfuscate(flag, tmp, "sub")) {
        change(tmp);
        return true;
    }

    return false;
}

bool Substitution::change(Function* f) {
    Function* tmp = f;

    //在函数上循环混淆指定次数
    int times = ObfTimes;
    do {
        for (Function::iterator bb = tmp->begin(); bb != tmp->end(); ++bb) {
            for (BasicBlock::iterator inst = bb->begin(); inst != bb->end(); ++inst) {
                if (inst->isBinaryOp()) {
                    switch (inst->getOpcode()) {
                    case BinaryOperator::Add:
                        //用随机加法替换
                        (this->*funcAdd[llvm::cryptoutils->get_range(NUMBER_ADD_SUBST)])(
                            cast<BinaryOperator>(inst));
                        ++Add;
                        break;
                    case BinaryOperator::Sub:
                        //随机减法替换
                        (this->*funcSub[llvm::cryptoutils->get_range(NUMBER_SUB_SUBST)])(
                            cast<BinaryOperator>(inst));
                        ++Sub;
                        break;
                    case BinaryOperator::Mul:
                        //随机整数乘法替换
                        (this->*funcMul[llvm::cryptoutils->get_range(NUMBER_MUL_SUBST)])(
                            cast<BinaryOperator>(inst));
                        ++Mul;
                        break;
                    case Instruction::And:
                        (this->*
                            funcAnd[llvm::cryptoutils->get_range(NUMBER_AND_SUBST)])(cast<BinaryOperator>(inst));
                        ++And;
                        break;
                    case Instruction::Or:
                        (this->*
                            funcOr[llvm::cryptoutils->get_range(NUMBER_OR_SUBST)])(cast<BinaryOperator>(inst));
                        ++Or;
                        break;
                    case Instruction::Xor:
                        (this->*
                            funcXor[llvm::cryptoutils->get_range(NUMBER_XOR_SUBST)])(cast<BinaryOperator>(inst));
                        ++Xor;
                        break;
                    case Instruction::Shl:
                        (this->*
                            funcShl[llvm::cryptoutils->get_range(NUMBER_SHL_SUBST)])(cast<BinaryOperator>(inst));
                        ++Shl;
                        break;
                    default:
                        break;
                    }  
                }    
            }  
        }  
    } while (--times > 0); 
    return false;
}

//实现a = b - (-c)
void Substitution::addNeg(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    //创建减法指令
    //指令只能判断是否为整数加法，但是能调用本函数的一定是加法，所以其他的进入浮点数加法
    if (bo->getOpcode() == Instruction::Add) {
        op = BinaryOperator::CreateNeg(bo->getOperand(1), "", bo);
        op =
            BinaryOperator::Create(Instruction::Sub, bo->getOperand(0), op, "", bo);

        //检查签名的换行
        //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
        //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());

        bo->replaceAllUsesWith(op);
    }/* else {
      op = BinaryOperator::CreateFNeg(bo->getOperand(1), "", bo);
      op = BinaryOperator::Create(Instruction::FSub, bo->getOperand(0), op, "",
                                  bo);
    }*/
}

//完成a = -(-b + (-c))
void Substitution::addDoubleNeg(BinaryOperator* bo) {
    BinaryOperator* op, * op2 = NULL;

    if (bo->getOpcode() == Instruction::Add) {
        op = BinaryOperator::CreateNeg(bo->getOperand(0), "", bo);
        op2 = BinaryOperator::CreateNeg(bo->getOperand(1), "", bo);
        op = BinaryOperator::Create(Instruction::Add, op, op2, "", bo);
        op = BinaryOperator::CreateNeg(op, "", bo);

        //检查签名换行
        //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
        //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());
    }
    else {
        op = BinaryOperator::CreateFNeg(bo->getOperand(0), "", bo);
        op2 = BinaryOperator::CreateFNeg(bo->getOperand(1), "", bo);
        op = BinaryOperator::Create(Instruction::FAdd, op, op2, "", bo);
        op = BinaryOperator::CreateFNeg(op, "", bo);
    }

    bo->replaceAllUsesWith(op);
}

//完成r = rand (); a = b + r; a = a + c; a = a - r
void Substitution::addRand(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    if (bo->getOpcode() == Instruction::Add) {
        Type* ty = bo->getType();
        ConstantInt* co =
            (ConstantInt*)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());
        op =
            BinaryOperator::Create(Instruction::Add, bo->getOperand(0), co, "", bo);
        op =
            BinaryOperator::Create(Instruction::Add, op, bo->getOperand(1), "", bo);
        op = BinaryOperator::Create(Instruction::Sub, op, co, "", bo);

        //检查签名换行
        //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
        //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());

        bo->replaceAllUsesWith(op);
    }
    /* else {
        Type *ty = bo->getType();
        ConstantFP *co =
    (ConstantFP*)ConstantFP::get(ty,(float)llvm::cryptoutils->get_uint64_t());
        op = BinaryOperator::Create(Instruction::FAdd,bo->getOperand(0),co,"",bo);
        op = BinaryOperator::Create(Instruction::FAdd,op,bo->getOperand(1),"",bo);
        op = BinaryOperator::Create(Instruction::FSub,op,co,"",bo);
    } */
}

//完成r = rand (); a = b - r; a = a + b; a = a + r
void Substitution::addRand2(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    if (bo->getOpcode() == Instruction::Add) {
        Type* ty = bo->getType();
        ConstantInt* co =
            (ConstantInt*)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());
        op =
            BinaryOperator::Create(Instruction::Sub, bo->getOperand(0), co, "", bo);
        op =
            BinaryOperator::Create(Instruction::Add, op, bo->getOperand(1), "", bo);
        op = BinaryOperator::Create(Instruction::Add, op, co, "", bo);

        // Check signed wrap
        //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
        //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());

        bo->replaceAllUsesWith(op);
    }
    /* else {
        Type *ty = bo->getType();
        ConstantFP *co =
    (ConstantFP*)ConstantFP::get(ty,(float)llvm::cryptoutils->get_uint64_t());
        op = BinaryOperator::Create(Instruction::FAdd,bo->getOperand(0),co,"",bo);
        op = BinaryOperator::Create(Instruction::FAdd,op,bo->getOperand(1),"",bo);
        op = BinaryOperator::Create(Instruction::FSub,op,co,"",bo);
    } */
}

//完成co = rand (); r = co + c; a = b + r; a = a + c; a = a - r;
void Substitution::addRand3(BinaryOperator* bo) {
    BinaryOperator* op, * op2 = NULL;

    if (bo->getOpcode() == Instruction::Add) {
        Type* ty = bo->getType();
        ConstantInt* co =
            (ConstantInt*)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());
        op2 = BinaryOperator::Create(Instruction::Add, co, bo->getOperand(1), "", bo);
        op =
            BinaryOperator::Create(Instruction::Add, bo->getOperand(0), op2, "", bo);
        op =
            BinaryOperator::Create(Instruction::Add, op, bo->getOperand(1), "", bo);
        op = BinaryOperator::Create(Instruction::Sub, op, op2, "", bo);

        // Check signed wrap
        //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
        //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());

        bo->replaceAllUsesWith(op);
    }
    /* else {
        Type* ty = bo->getType();
        ConstantFP* co =
            (ConstantFP*)ConstantFP::get(ty, llvm::cryptoutils->get_uint64_t());
        op2 = BinaryOperator::Create(Instruction::FAdd, co, bo->getOperand(1), "", bo);
        op =
            BinaryOperator::Create(Instruction::FAdd, bo->getOperand(0), op2, "", bo);
        op =
            BinaryOperator::Create(Instruction::FAdd, op, bo->getOperand(1), "", bo);
        op = BinaryOperator::Create(Instruction::FSub, op, op2, "", bo);
    } */
}

//完成a = b + (-c)
void Substitution::subNeg(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    if (bo->getOpcode() == Instruction::Sub) {
        op = BinaryOperator::CreateNeg(bo->getOperand(1), "", bo);
        op =
            BinaryOperator::Create(Instruction::Add, bo->getOperand(0), op, "", bo);

        // Check signed wrap
        //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
        //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());
    }
    else {
        op = BinaryOperator::CreateFNeg(bo->getOperand(1), "", bo);
        op = BinaryOperator::Create(Instruction::FAdd, bo->getOperand(0), op, "",
            bo);
    }

    bo->replaceAllUsesWith(op);
}

//完成a = -((-b) - (-c))
void Substitution::subDoubleNeg(BinaryOperator* bo) {
    BinaryOperator* op, * op2 = NULL;

    if (bo->getOpcode() == Instruction::Sub) {
        op = BinaryOperator::CreateNeg(bo->getOperand(0), "", bo);
        op2 = BinaryOperator::CreateNeg(bo->getOperand(1), "", bo);
        op =
            BinaryOperator::Create(Instruction::Sub, op, op2, "", bo);
        op = BinaryOperator::CreateNeg(op, "", bo);

        // Check signed wrap
        //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
        //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());
    }
    else {
        op = BinaryOperator::CreateFNeg(bo->getOperand(0), "", bo);
        op2 = BinaryOperator::CreateFNeg(bo->getOperand(1), "", bo);
        op =
            BinaryOperator::Create(Instruction::FSub, op, op2, "", bo);
        op = BinaryOperator::CreateFNeg(op, "", bo);
    }

    bo->replaceAllUsesWith(op);
}

//完成 r = rand (); a = b + r; a = a - c; a = a - r
void Substitution::subRand(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    if (bo->getOpcode() == Instruction::Sub) {
        Type* ty = bo->getType();
        ConstantInt* co =
            (ConstantInt*)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());
        op =
            BinaryOperator::Create(Instruction::Add, bo->getOperand(0), co, "", bo);
        op =
            BinaryOperator::Create(Instruction::Sub, op, bo->getOperand(1), "", bo);
        op = BinaryOperator::Create(Instruction::Sub, op, co, "", bo);

        // Check signed wrap
        //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
        //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());

        bo->replaceAllUsesWith(op);
    }
    /* else {
        Type *ty = bo->getType();
        ConstantFP *co =
    (ConstantFP*)ConstantFP::get(ty,(float)llvm::cryptoutils->get_uint64_t());
        op = BinaryOperator::Create(Instruction::FAdd,bo->getOperand(0),co,"",bo);
        op = BinaryOperator::Create(Instruction::FSub,op,bo->getOperand(1),"",bo);
        op = BinaryOperator::Create(Instruction::FSub,op,co,"",bo);
    } */
}

//完成 r = rand (); a = b - r; a = a - c; a = a + r
void Substitution::subRand2(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    if (bo->getOpcode() == Instruction::Sub) {
        Type* ty = bo->getType();
        ConstantInt* co =
            (ConstantInt*)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());
        op =
            BinaryOperator::Create(Instruction::Sub, bo->getOperand(0), co, "", bo);
        op =
            BinaryOperator::Create(Instruction::Sub, op, bo->getOperand(1), "", bo);
        op = BinaryOperator::Create(Instruction::Add, op, co, "", bo);

        // Check signed wrap
        //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
        //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());

        bo->replaceAllUsesWith(op);
    }
    /* else {
        Type *ty = bo->getType();
        ConstantFP *co =
    (ConstantFP*)ConstantFP::get(ty,(float)llvm::cryptoutils->get_uint64_t());
        op = BinaryOperator::Create(Instruction::FSub,bo->getOperand(0),co,"",bo);
        op = BinaryOperator::Create(Instruction::FSub,op,bo->getOperand(1),"",bo);
        op = BinaryOperator::Create(Instruction::FAdd,op,co,"",bo);
    } */
}

//a=b*(c+2)-2b;
void Substitution::Mul1(BinaryOperator* bo) {
    BinaryOperator* op = NULL;
    BinaryOperator* op1 = NULL;

    if (bo->getOpcode() == Instruction::Mul) {
        Type* ty = bo->getType();
        ConstantInt* co =
            (ConstantInt*)ConstantInt::get(ty, 2);
        op =
            BinaryOperator::Create(Instruction::Mul, bo->getOperand(0), co, "", bo);
        op1 =
            BinaryOperator::Create(Instruction::Add, bo->getOperand(1), co, "", bo);
        op1 =
            BinaryOperator::Create(Instruction::Mul, bo->getOperand(0), op1, "", bo);
        op =
            BinaryOperator::Create(Instruction::Sub, op1, op, "", bo);

        bo->replaceAllUsesWith(op);
    }
}

//c<<2;a=bc;a>>2;
void Substitution::Mul2(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    if (bo->getOpcode() == Instruction::Mul) {
        Type* ty = bo->getType();
        ConstantInt* co =
            (ConstantInt*)ConstantInt::get(ty, 2);
        op =
            BinaryOperator::Create(Instruction::Shl, bo->getOperand(1), co, "", bo);
        op =
            BinaryOperator::Create(Instruction::Mul, op, bo->getOperand(0), "", bo);
        op = BinaryOperator::Create(Instruction::AShr, op, co, "", bo);

        // Check signed wrap
        //op->setHasNoSignedWrap(bo->hasNoSignedWrap());
        //op->setHasNoUnsignedWrap(bo->hasNoUnsignedWrap());

        bo->replaceAllUsesWith(op);
    }
    /* else {
        Type *ty = bo->getType();
        ConstantFP *co =
    (ConstantFP*)ConstantFP::get(ty,(float)llvm::cryptoutils->get_uint64_t());
        op = BinaryOperator::Create(Instruction::FSub,bo->getOperand(0),co,"",bo);
        op = BinaryOperator::Create(Instruction::FSub,op,bo->getOperand(1),"",bo);
        op = BinaryOperator::Create(Instruction::FAdd,op,co,"",bo);
    } */
}

//完成a = b & c => a = (b^~c)& b
void Substitution::andSubstitution(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    op = BinaryOperator::CreateNot(bo->getOperand(1), "", bo);

    BinaryOperator* op1 =
        BinaryOperator::Create(Instruction::Xor, bo->getOperand(0), op, "", bo);

    // Create AND => (b^~c) & b
    op = BinaryOperator::Create(Instruction::And, op1, bo->getOperand(0), "", bo);
    bo->replaceAllUsesWith(op);
}

//完成 a = a && b <=> !(!a | !b) && (r | !r)
void Substitution::andSubstitutionRand(BinaryOperator* bo) {
    // Copy of the BinaryOperator type to create the random number with the
    // same type of the operands
    Type* ty = bo->getType();

    // r (Random number)
    ConstantInt* co =
        (ConstantInt*)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());

    // !a
    BinaryOperator* op = BinaryOperator::CreateNot(bo->getOperand(0), "", bo);

    // !b
    BinaryOperator* op1 = BinaryOperator::CreateNot(bo->getOperand(1), "", bo);

    // !r
    BinaryOperator* opr = BinaryOperator::CreateNot(co, "", bo);

    // (!a | !b)
    BinaryOperator* opa =
        BinaryOperator::Create(Instruction::Or, op, op1, "", bo);

    // (r | !r)
    opr = BinaryOperator::Create(Instruction::Or, co, opr, "", bo);

    // !(!a | !b)
    op = BinaryOperator::CreateNot(opa, "", bo);

    // !(!a | !b) && (r | !r)
    op = BinaryOperator::Create(Instruction::And, op, opr, "", bo);

    // We replace all the old AND operators with the new one transformed
    bo->replaceAllUsesWith(op);
}

//完成 a = b | c => a = (b & c) | (b ^ c)
void Substitution::orSubstitutionRand(BinaryOperator* bo) {

    Type* ty = bo->getType();
    ConstantInt* co =
        (ConstantInt*)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());

    // !a
    BinaryOperator* op = BinaryOperator::CreateNot(bo->getOperand(0), "", bo);

    // !b
    BinaryOperator* op1 = BinaryOperator::CreateNot(bo->getOperand(1), "", bo);

    // !r
    BinaryOperator* op2 = BinaryOperator::CreateNot(co, "", bo);

    // !a && r
    BinaryOperator* op3 =
        BinaryOperator::Create(Instruction::And, op, co, "", bo);

    // a && !r
    BinaryOperator* op4 =
        BinaryOperator::Create(Instruction::And, bo->getOperand(0), op2, "", bo);

    // !b && r
    BinaryOperator* op5 =
        BinaryOperator::Create(Instruction::And, op1, co, "", bo);

    // b && !r
    BinaryOperator* op6 =
        BinaryOperator::Create(Instruction::And, bo->getOperand(1), op2, "", bo);

    // (!a && r) || (a && !r)
    op3 = BinaryOperator::Create(Instruction::Or, op3, op4, "", bo);

    // (!b && r) ||(b && !r)
    op4 = BinaryOperator::Create(Instruction::Or, op5, op6, "", bo);

    // (!a && r) || (a && !r) ^ (!b && r) ||(b && !r)
    op5 = BinaryOperator::Create(Instruction::Xor, op3, op4, "", bo);

    // !a || !b
    op3 = BinaryOperator::Create(Instruction::Or, op, op1, "", bo);

    // !(!a || !b)
    op3 = BinaryOperator::CreateNot(op3, "", bo);

    // r || !r
    op4 = BinaryOperator::Create(Instruction::Or, co, op2, "", bo);

    // !(!a || !b) && (r || !r)
    op4 = BinaryOperator::Create(Instruction::And, op3, op4, "", bo);

    // [(!a && r) || (a && !r) ^ (!b && r) ||(b && !r) ] || [!(!a || !b) && (r ||
    // !r)]
    op = BinaryOperator::Create(Instruction::Or, op5, op4, "", bo);
    bo->replaceAllUsesWith(op);
}

void Substitution::orSubstitution(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    // Creating first operand (b & c)
    op = BinaryOperator::Create(Instruction::And, bo->getOperand(0),
        bo->getOperand(1), "", bo);

    // Creating second operand (b ^ c)
    BinaryOperator* op1 = BinaryOperator::Create(
        Instruction::Xor, bo->getOperand(0), bo->getOperand(1), "", bo);

    // final op
    op = BinaryOperator::Create(Instruction::Or, op, op1, "", bo);
    bo->replaceAllUsesWith(op);
}

//完成a = a ~ b => a = (!a && b) || (a && !b)
void Substitution::xorSubstitution(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    // Create NOT on first operand
    op = BinaryOperator::CreateNot(bo->getOperand(0), "", bo); // !a

    // Create AND
    op = BinaryOperator::Create(Instruction::And, bo->getOperand(1), op, "",
        bo); // !a && b

// Create NOT on second operand
    BinaryOperator* op1 =
        BinaryOperator::CreateNot(bo->getOperand(1), "", bo); // !b

    // Create AND
    op1 = BinaryOperator::Create(Instruction::And, bo->getOperand(0), op1, "",
        bo); // a && !b

// Create OR
    op = BinaryOperator::Create(Instruction::Or, op, op1, "",
        bo); // (!a && b) || (a && !b)
    bo->replaceAllUsesWith(op);
}

//完成a = a ^ b <=> (a ^ r) ^ (b ^ r) <=> (!a && r || a && !r) ^
// (!b && r || b && !r)
// note : r is a random number
void Substitution::xorSubstitutionRand(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    Type* ty = bo->getType();
    ConstantInt* co =
        (ConstantInt*)ConstantInt::get(ty, llvm::cryptoutils->get_uint64_t());

    // !a
    op = BinaryOperator::CreateNot(bo->getOperand(0), "", bo);

    // !a && r
    op = BinaryOperator::Create(Instruction::And, co, op, "", bo);

    // !r
    BinaryOperator* opr = BinaryOperator::CreateNot(co, "", bo);

    // a && !r
    BinaryOperator* op1 =
        BinaryOperator::Create(Instruction::And, bo->getOperand(0), opr, "", bo);

    // !b
    BinaryOperator* op2 = BinaryOperator::CreateNot(bo->getOperand(1), "", bo);

    // !b && r
    op2 = BinaryOperator::Create(Instruction::And, op2, co, "", bo);

    // b && !r
    BinaryOperator* op3 =
        BinaryOperator::Create(Instruction::And, bo->getOperand(1), opr, "", bo);

    // (!a && r) || (a && !r)
    op = BinaryOperator::Create(Instruction::Or, op, op1, "", bo);

    // (!b && r) || (b && !r)
    op1 = BinaryOperator::Create(Instruction::Or, op2, op3, "", bo);

    // (!a && r) || (a && !r) ^ (!b && r) || (b && !r)
    op = BinaryOperator::Create(Instruction::Xor, op, op1, "", bo);
    bo->replaceAllUsesWith(op);
}

//a=b<<(c-2)*4
void Substitution::Shl1(BinaryOperator* bo) {
    BinaryOperator* op = NULL;

    if (bo->getOpcode() == Instruction::Shl) {
        Type* ty = bo->getType();
        ConstantInt* co =
            (ConstantInt*)ConstantInt::get(ty, 2);
        ConstantInt* co2 =
            (ConstantInt*)ConstantInt::get(ty, 4);
        op =
            BinaryOperator::Create(Instruction::Sub, bo->getOperand(1), co, "", bo);
        op =
            BinaryOperator::Create(Instruction::Shl, bo->getOperand(0), op, "", bo);
        op =
            BinaryOperator::Create(Instruction::Mul, co2, op, "", bo);

        bo->replaceAllUsesWith(op);
    }
}

//op=b*4;op2=c-2;a=op<<op2
void Substitution::Shl2(BinaryOperator* bo) {
    BinaryOperator* op = NULL;
    BinaryOperator* op2 = NULL;
    Type* ty = bo->getType();
    ConstantInt* co =
        (ConstantInt*)ConstantInt::get(ty, 4);
    ConstantInt* co2 =
        (ConstantInt*)ConstantInt::get(ty, 2);

    if (bo->getOpcode() == Instruction::Shl) {
        
        op =
            BinaryOperator::Create(Instruction::Mul, bo->getOperand(0), co, "", bo);
        op2 =
            BinaryOperator::Create(Instruction::Sub, bo->getOperand(1), co2, "", bo);
        op =
            BinaryOperator::Create(Instruction::Shl, op, op2, "", bo);
        bo->replaceAllUsesWith(op);
    }
}
