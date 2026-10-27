/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.Paper.ConstantCompletionRestriction
public import Sheaf.Paper.ConstantCompletionInverseImageExists
public import Sheaf.Paper.ConstantCompletionCompletedFinitePull
public import Sheaf.Paper.ConstantCompletionPullbackTowerComparison
public import Sheaf.Paper.ConstantCompletionPullbackComposition
public import Sheaf.Paper.ConstantCompletionPullbackIdentity

/-!
# Constant coefficients and their sheafwise adic completion

Source: Stacks Project, Tags 093M, 099I, 099L, 099M, 0A0E, 06YY and 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence).

Positive exponents are indexed by `n : ℕ`, meaning `n+1`. All localizations below use
Mathlib's standard derived category. The extra names only specify the canonical objects,
strict towers and representative normalizations in this node; they introduce no replacement

The declarations live in the modules `Sheaf.Paper.ConstantCompletion*` imported above (split
on 2026-10-27 so that each sorried theorem has its own module); this module re-exports them.
Their private helpers are reached with `import all` of the part that defines them
(`Sheaf.Paper.ConstantCompletionCore`, `...InverseImage`, `...DerivedPull`, `...FinitePull`).
-/

@[expose] public noncomputable section

namespace CategoryTheory.ConstantCompletion

attribute [instance] restrictionReduction_additive reductionRestriction_additive
  reductionRestriction_preservesZero

end CategoryTheory.ConstantCompletion
