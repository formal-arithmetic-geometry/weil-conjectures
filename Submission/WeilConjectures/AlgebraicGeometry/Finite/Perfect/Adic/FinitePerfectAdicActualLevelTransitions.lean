/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicConstantNormalization
public import Submission.WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicStalkModels
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
import Submission.WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes
import Submission.WeilConjectures.AlgebraicGeometry.DerivedCategories
import Submission.WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
import Submission.WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import Submission.WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import Submission.WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleSheaf
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

set_option autoImplicit true
set_option relaxedAutoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 3

/-! # Consecutive normalized arrows for actual finite levels

Source: Stacks Project, Tags 09C6 and 06YY.
(blueprint: lem-weil-pbc-finite-perfect-adic-actual-level-transitions).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

end AlgebraicGeometry.Scheme
