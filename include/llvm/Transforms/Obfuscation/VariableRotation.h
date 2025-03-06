#ifndef _VARIABLEROTATION_H_
#define _VARIABLEROTATION_H_

#include "llvm/Pass.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/CFG.h"
#include "llvm/ADT/MapVector.h"
#include "llvm/ADT/SetVector.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/LegacyPassManager.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/IPO/PassManagerBuilder.h"

// Namespace
using namespace std;

namespace llvm {
	Pass* createVariableRotation();
	Pass* createVariableRotation(bool flag);
}

#endif
