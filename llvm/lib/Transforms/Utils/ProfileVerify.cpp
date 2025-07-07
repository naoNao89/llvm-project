//===- ProfileVerify.cpp - Verify profile info for testing ----------------===//
//
// Part of the LLVM Project, under the Apache License v2.0 with LLVM Exceptions.
// See https://llvm.org/LICENSE.txt for license information.
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
//
//===----------------------------------------------------------------------===//

#include "llvm/Transforms/Utils/ProfileVerify.h"
#include "llvm/ADT/DynamicAPInt.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/STLExtras.h"
#include "llvm/Analysis/BranchProbabilityInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/Analysis.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/MDBuilder.h"
#include "llvm/IR/ProfDataUtils.h"
#include "llvm/Support/BranchProbability.h"

using namespace llvm;
namespace {
class ProfileInjector {
  Function &F;
  FunctionAnalysisManager &FAM;

public:
  static const Instruction *
  getTerminatorBenefitingFromMDProf(const BasicBlock &BB) {
    if (succ_size(&BB) < 2)
      return nullptr;
    auto *Term = BB.getTerminator();
    return (isa<BranchInst>(Term) || isa<SwitchInst>(Term) ||
            isa<IndirectBrInst>(Term) || isa<CallBrInst>(Term))
               ? Term
               : nullptr;
  }

  static Instruction *getTerminatorBenefitingFromMDProf(BasicBlock &BB) {
    return const_cast<Instruction *>(
        getTerminatorBenefitingFromMDProf(const_cast<const BasicBlock &>(BB)));
  }

  ProfileInjector(Function &F, FunctionAnalysisManager &FAM) : F(F), FAM(FAM) {}
  bool inject();
};
} // namespace

// FIXME: currently this injects only for terminators. Select isn't yet
// supported.
bool ProfileInjector::inject() {
  auto &BPI = FAM.getResult<BranchProbabilityAnalysis>(F);

  bool Changed = false;
  for (auto &BB : F) {
    auto *Term = getTerminatorBenefitingFromMDProf(BB);
    if (!Term || Term->getMetadata(LLVMContext::MD_prof))
      continue;
    SmallVector<BranchProbability> Probs;
    Probs.reserve(Term->getNumSuccessors());
    for (auto I = 0U, E = Term->getNumSuccessors(); I < E; ++I)
      Probs.emplace_back(BPI.getEdgeProbability(&BB, Term->getSuccessor(I)));

    const auto *FirstZeroDenominator =
        find_if(Probs, [](const BranchProbability &P) {
          return P.getDenominator() == 0;
        });
    (void)FirstZeroDenominator;
    assert(FirstZeroDenominator == Probs.end());
    const auto *FirstNonZeroNumerator =
        find_if(Probs, [](const BranchProbability &P) {
          return !P.isZero() && !P.isUnknown();
        });
    assert(FirstNonZeroNumerator != Probs.end());
    DynamicAPInt LCM(Probs[0].getDenominator());
    DynamicAPInt GCD(FirstNonZeroNumerator->getNumerator());
    for (const auto &Prob : drop_begin(Probs)) {
      if (!Prob.getNumerator())
        continue;
      LCM = llvm::lcm(LCM, DynamicAPInt(Prob.getDenominator()));
      GCD = llvm::gcd(GCD, DynamicAPInt(Prob.getNumerator()));
    }
    SmallVector<uint32_t> Weights;
    Weights.reserve(Term->getNumSuccessors());
    for (const auto &Prob : Probs) {
      DynamicAPInt W =
          (Prob.getNumerator() * LCM / GCD) / Prob.getDenominator();
      Weights.emplace_back(static_cast<uint32_t>((int64_t)W));
    }
    setBranchWeights(*Term, Weights, /*IsExpected=*/false);
    Changed = true;
  }
  return Changed;
}

PreservedAnalyses ProfileInjectorPass::run(Function &F,
                                           FunctionAnalysisManager &FAM) {
  ProfileInjector PI(F, FAM);
  if (!PI.inject())
    return PreservedAnalyses::all();

  return PreservedAnalyses::none();
}

PreservedAnalyses ProfileVerifierPass::run(Function &F,
                                           FunctionAnalysisManager &FAM) {
  for (const auto &BB : F)
    if (const auto *Term =
            ProfileInjector::getTerminatorBenefitingFromMDProf(BB))
      if (!Term->getMetadata(LLVMContext::MD_prof))
        F.getContext().emitError("Profile verification failed");

  return PreservedAnalyses::none();
}
