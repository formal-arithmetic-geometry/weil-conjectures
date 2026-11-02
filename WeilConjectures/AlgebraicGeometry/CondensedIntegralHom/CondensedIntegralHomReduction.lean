/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation

import WeilConjectures.ProEtaleCoefficients.PrincipalConeTensorNormalization
import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomAdjunction
import WeilConjectures.CategoryTheory.RingedHomUniverses.RingedInternalHomShiftOfUniversesSupplement
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

/-! # Integral internal Hom and reduction for continuous condensed coefficients

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-tower/
lem-coef-integral-hom-reduction.md and its proof, order 2975
(blueprint: lem-coef-integral-hom-reduction).

The positive coefficient level n+1 is indexed by n : ℕ, as in AdicCompletion.
The comparison is the transpose of scalar extension of the actual evaluation,
using the canonical derived tensor comparison. No completeness of the source,
constructibility, boundedness, or perfectness is assumed.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedIntegralHom

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (X : Scheme.{u})

/-- The canonical K-flat scalar tensor isomorphism at positive coefficient level n+1.
It derives the ordinary balanced scalar tensorator, whose inverse multiplies the
scalar factors. Scalar extension need not be exact.
Source: blueprint proof, first paragraph, scalar extension of evaluation
(blueprint: lem-coef-integral-hom-reduction). -/
def reductionTensorIso (n : ℕ) (K L : DerivedCategory (AdicCompletion.Modules l E X)) :
    (AdicCompletion.derivedReduction l E X n).obj (K ⊗ L) ≅
      (AdicCompletion.derivedReduction l E X n).obj K ⊗
        (AdicCompletion.derivedReduction l E X n).obj L :=
  letI := Mod.extendScalarsMonoidal (AdicCompletion.quotient l E X n)
  letI := Mod.extendScalars_preservesFlat (AdicCompletion.quotient l E X n)
  let τ := asIso
    (Mod.extendScalars (AdicCompletion.quotient l E X n)).leftDerivedTensorComparison
  (τ.app K).app L

/-- Scalar extension of the integral evaluation, after canonical tensor reassociation.
Source: blueprint proof, first paragraph, the evaluation defining c_n
(blueprint: lem-coef-integral-hom-reduction). -/
def reductionEvaluation (n : ℕ) (K L : DerivedCategory (AdicCompletion.Modules l E X)) :
    (AdicCompletion.derivedReduction l E X n).obj K ⊗
        (AdicCompletion.derivedReduction l E X n).obj
          (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj (op K)).obj L) ⟶
      (AdicCompletion.derivedReduction l E X n).obj L :=
  (reductionTensorIso l E X n K
    (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj (op K)).obj L)).inv ≫
      (AdicCompletion.derivedReduction l E X n).map
        ((CondensedRing.derivedTensorHomAdjunction
          (DerivedNakayama.integerRing l E) K).counit.app L)

/-- The canonical A_(n+1)-linear Hom reduction arrow, defined by transposing evaluation.
Its invertibility is a conclusion, not part of its construction.
Source: blueprint statement and proof, first paragraph
(blueprint: lem-coef-integral-hom-reduction). -/
def comparison (n : ℕ) (K L : DerivedCategory (AdicCompletion.Modules l E X)) :
    (AdicCompletion.derivedReduction l E X n).obj
        (((CondensedRing.derivedHom (DerivedNakayama.integerRing l E) X).obj (op K)).obj L) ⟶
      ((CondensedRing.derivedHom (DerivedNakayama.quotientRing l E (n + 1)) X).obj
        (op ((AdicCompletion.derivedReduction l E X n).obj K))).obj
          ((AdicCompletion.derivedReduction l E X n).obj L) :=
  (CondensedRing.derivedTensorHomAdjunction (DerivedNakayama.quotientRing l E (n + 1))
    ((AdicCompletion.derivedReduction l E X n).obj K)).homEquiv _ _
      (reductionEvaluation l E X n K L)

end AlgebraicGeometry.ProEtale.CondensedIntegralHom
