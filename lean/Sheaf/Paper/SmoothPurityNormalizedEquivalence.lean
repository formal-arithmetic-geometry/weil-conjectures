/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NK
-/
module

public import Sheaf.Paper.SmoothPurityReductionTowerNormalized
public import Sheaf.Paper.SmoothPurityTowerReconstruction
public import Sheaf.Paper.DerivedCompleteOnSlices
public import Sheaf.Paper.CoefficientRingedSequenceSite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Scheme
public import Sheaf.Paper.CompletedIntegralConstantMapOfUniverses
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Sheaf.Paper.SmoothPurityCoefficientTowers
public import Sheaf.Paper.SmoothPurityNormalizedTowers
public import Sheaf.Paper.FiniteTorAmplitude
public import Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude
public import Sheaf.Paper.SfIntegralConstructible
public import Sheaf.Paper.SfDerivedComplete
public import Sheaf.Paper.CompletedDerivedInverseLimit
public import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
public import Mathlib.RingTheory.Noetherian.Defs
import Sheaf.NumberTheory.Padics.ExtensionIntegersDvr
import Sheaf.CategoryTheory.SystemLevelLeftExtension
import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import Mathlib.CategoryTheory.Limits.Final
import Mathlib.CategoryTheory.IsConnected
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Sheaf.Paper.NormalizedDVRTower
import Sheaf.Paper.NormalizedDVREffectivity
import Sheaf.Algebra.Homology.ChangeOfRingsKFlat
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Sheaf.Paper.IntrinsicFiniteTorsionConstructibility
import Sheaf.Paper.ProEtaleConstructibleSheaf
import Sheaf.Paper.IntegralResidueTor

import Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport
import Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction
import Sheaf.Paper.FiniteFieldFiber
/-!
# Normalized coefficient towers and derived-complete integral complexes

Source: blueprint main-20261015, sec-smooth-purity,
`sk-lem-sp-tower/sk-lem-sp-tower-equivalence.md`; Bhatt--Scholze, Lemma 3.5.7
(blueprint: det-sp-normalized-equivalence).

## Main definitions and statements

- `spCompletedReduction`: the existing reduction transported to completed coefficients.
- `spCompletedTotalLimit`: exact scalar forgetting followed by total derived inverse limit.
- `spCompletedTotalProjection`: the resolution-normalized limit projections.
- `SpNormalizedEquivalence`: the adjunction, its isomorphisms, and constructible restriction.
- `sp_normalized_equivalence`: existence of this normalized equivalence data.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] (T : Scheme.{u})

/-- Forget the finite-level actions to completed coefficients, retaining all strict
transitions. Source: blueprint, definition of L_T (blueprint: det-sp-normalized-equivalence). -/
def spCompletedStrictTower (D : SpCoefficientTowersAbelian l E T) :
    spCoefficientTowers l E T ⥤
      (ℕᵒᵖ ⥤ WeilConjectures.scalarReductionSource.{u, u} l E T) :=
  (Functor.ofOpSequence (spCompletedTransition l E T D)).flip

/-- The coefficient-ring identification transports the existing reduction functor
from section modules to modules over the completed ring. Source: blueprint, r_T
(blueprint: det-sp-normalized-equivalence). -/
def spCompletedReduction (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) :
    DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) ⥤
      spDerivedCoefficientTowers l E T D :=
  (restrictScalars.{u + 1}
    ((sheafCompose _ (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map
      R.coefficient.hom)).mapDerivedCategory ⋙ R.red

/-- Total derived inverse limit after the exact scalar-forgetting functor. The
fixed-ring limit is the existing K-injective total derived inverse limit, including its
resolution-normalized projections. Source: blueprint, L_T; Stacks 0941
(blueprint: det-sp-normalized-equivalence). -/
def spCompletedTotalLimit (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] :
    spDerivedCoefficientTowers l E T D ⥤
      DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T) :=
  letI := D.hasDerived
  (spCompletedStrictTower l E T D).mapDerivedCategory ⋙
    WeilConjectures.coefficientConstantTowerLimit l E T

/-- Exact evaluation commutes with forgetting the finite-level coefficient actions.
The comparison is the canonical localization comparison for the two exact composites.
Source: blueprint, definition of L_T (blueprint: det-sp-normalized-equivalence). -/
def spCompletedForgettingEvaluationIso (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] (n : ℕ) :
    @Functor.mapDerivedCategory _ _ _ D.hasDerived _ _ _
        (HasDerivedCategory.standard _) (spCompletedStrictTower l E T D) _ _ _ ⋙
      WeilConjectures.coefficientConstantTowerEvaluation l E T n ≅
        spDerivedCompletedEvaluation l E T D n :=
  letI := D.hasDerived
  letI := D.evaluationLimits n
  letI := D.evaluationColimits n
  letI : (spCoefficientEvaluation l E T D.equivalence n).Additive :=
    Functor.additive_of_preserves_binary_products _
  (Functor.mapDerivedCategoryCompIso (spCompletedStrictTower l E T D)
    ((evaluation ℕᵒᵖ (WeilConjectures.scalarReductionSource l E T)).obj (op n))).symm ≪≫
    Functor.mapDerivedCategoryCompIso (spCoefficientEvaluation l E T D.equivalence n)
      (spCompletedEllRestriction l E T n)

/-- The actual total-limit projection to each completed-coefficient level. Its
normalization comes from the existing projection on simultaneous K-injective towers.
Source: blueprint, total limit and its counit (blueprint: det-sp-normalized-equivalence). -/
def spCompletedTotalProjection (D : SpCoefficientTowersAbelian l E T)
    [(spCompletedStrictTower l E T D).Additive]
    [PreservesFiniteLimits (spCompletedStrictTower l E T D)]
    [PreservesFiniteColimits (spCompletedStrictTower l E T D)] (n : ℕ) :
    spCompletedTotalLimit l E T D ⟶ spDerivedCompletedEvaluation l E T D n :=
  letI := D.hasDerived
  Functor.whiskerLeft (spCompletedStrictTower l E T D).mapDerivedCategory
    (WeilConjectures.coefficientConstantTowerProjection l E T n) ≫
      (spCompletedForgettingEvaluationIso l E T D n).hom

/-- The ambient reduction/total-limit adjunction, its isomorphisms on complete and
normalized objects, and its restriction to the recorded constructible categories.
Exact scalar forgetting is part of the construction, not an additional hypothesis.
Source: blueprint, normalized equivalence; Bhatt--Scholze, Lemma 3.5.7
(blueprint: det-sp-normalized-equivalence). -/
structure SpNormalizedEquivalence (D : SpCoefficientTowersAbelian l E T)
    (R : SpReductionTower l E T D) where
  /-- Forgetting actions preserves componentwise addition. -/
  [forgetAdditive : (spCompletedStrictTower l E T D).Additive]
  /-- Forgetting actions preserves kernels and finite products. -/
  [forgetLimits : PreservesFiniteLimits (spCompletedStrictTower l E T D)]
  /-- Forgetting actions preserves cokernels and finite coproducts. -/
  [forgetColimits : PreservesFiniteColimits (spCompletedStrictTower l E T D)]
  /-- Total derived limit is exact, with its standard integer shift structure. -/
  [limitShift : (spCompletedTotalLimit l E T D).CommShift ℤ]
  /-- It carries distinguished triangles to distinguished triangles. -/
  limit_triangulated : (spCompletedTotalLimit l E T D).IsTriangulated
  /-- The products in the Roos triangle are products in the derived category. -/
  [products : HasCountableProducts
    (DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T))]
  /-- The Roos triangle uses the actual derived strict-tower transitions and the
  K-injective-normalized projections; it chooses no arbitrary lift from a triangle. -/
  roos : ∀ C : spDerivedCoefficientTowers l E T D,
    ∃ δ : (∏ᶜ fun n : ℕ ↦ (spDerivedCompletedEvaluation l E T D n).obj C) ⟶
        ((spCompletedTotalLimit l E T D).obj C)⟦(1 : ℤ)⟧,
      IsDerivedLimitTriangle
        (fun n : ℕ ↦ (spDerivedCompletedTransition l E T D n).app C)
        ((spCompletedTotalLimit l E T D).obj C)
        (Pi.lift (fun n : ℕ ↦ (spCompletedTotalProjection l E T D n).app C)) δ
  /-- The ambient adjunction on the ordinary unbounded derived categories. -/
  adjunction : spCompletedReduction l E T D R ⊣ spCompletedTotalLimit l E T D
  /-- No boundedness or constructibility is assumed on a derived-complete object. -/
  unit_isIso : ∀ M : DerivedCategory (WeilConjectures.scalarReductionSource.{u, u} l E T),
    WeilConjectures.IntegralOnSlice.IsComplete l E T none M →
      IsIso (adjunction.unit.app M)
  /-- No boundedness or constructibility is assumed on a normalized tower. -/
  counit_isIso : ∀ C : spDerivedCoefficientTowers l E T D,
    IsSpNormalizedTower l E T D C → IsIso (adjunction.counit.app C)
  /-- Only the constructible restriction assumes that T is Noetherian. The two
  equalities say that these are precisely the restrictions of reduction and total limit. -/
  restriction : IsNoetherian T →
    ∃ e : WeilConjectures.sfIntegralConstructibleCategory l E T ≌
        spNormalizedConstructibleTorTowerCategory l E T D,
      e.functor ⋙ (spNormalizedConstructibleTorTowers l E T D).ι =
        (WeilConjectures.sfIntegralConstructible l E T).ι ⋙ spCompletedReduction l E T D R ∧
      e.inverse ⋙ (WeilConjectures.sfIntegralConstructible l E T).ι =
        (spNormalizedConstructibleTorTowers l E T D).ι ⋙ spCompletedTotalLimit l E T D

/-- Reduction is left adjoint to total derived inverse limit, its unit is invertible
on derived-complete objects, and its counit on all normalized towers. On a Noetherian
scheme this restricts to the mutually inverse constructible equivalences.
Source: blueprint main-20261015, sk-lem-sp-tower-equivalence; Bhatt--Scholze,
Lemma 3.5.7(1)--(5) (blueprint: det-sp-normalized-equivalence).

Proof, following the ten DAG steps:
1. The DVR decomposition ell = unit times pi^e, e >= 1
(lem-weil-l-adic-extension-integers-dvr), identifies ell-power quotients with the
cofinal pi-power levels en. Use the actual strict system and the unbounded
uniformizer reduction/limit adjunction of lem-coef-derived-system-evaluation-calculus.
2. On fixed-ring towers, subsequence restriction has the exact ceiling-index left
adjoint, hence preserves K-injectives. Initiality of the subsequence gives the
projection-preserving total-limit isomorphism by lem-weil-pbc-initial-functor-limit
and lem-weil-pbc-ringed-strict-tower-homotopy-limit, with no product-exactness assumption.
3. On varying coefficients restriction has the exact floor-index right adjoint,
zero below e. Its Hom bijections descend to unbounded derived categories by
lem-sf-exact-functor-derived-triangulated; the selected composite is the identity.
4. Compose these Hom bijections with the uniformizer adjunction. Their naturality
gives the ambient adjunction. Its unit comes from strict quotient maps and its
counit is the tensor adjunct of the actual limit projections.
5. Use lem-pur-system-level-left-extension to interpolate any normalized ell-power
tower to the uniformizer levels. The ceiling formula, tensor associators, and
normalization make every transition-adjoint an isomorphism, including equal indices.
6. Apply lem-coef-normalized-dvr-effectivity to that tower. Its level comparisons are
the counit of step 4; derived evaluations detect isomorphisms. This proves the
counit clause without boundedness, Tor bounds or constructibility.
7. The reduction tower of every complex is normalized by K-flat change of rings
(lem-pur-kflat-change-of-rings). Effectivity and the triangular identity make the
unit at its completion invertible. For a derived-complete M, compare its augmented
Roos triangle with the total-limit triangle using TR3 and lem-sf-triangle-morphism-iso.
This gives M isomorphic to its completion. Naturality of the unit then makes its
actual component at M invertible; cofinality respects the quotient-map units.
8. Integral constructibility supplies constructible uniformizer reductions and a
common cohomological interval. Select the en levels and use lem-coef-integral-residue-tor
for a common Tor interval. The arbitrary-complex construction in
det-sp-reduction-tower-normalized supplies the strict normalized reduction tower.
Thus reduction lands in the recorded normalized constructible finite-Tor subcategory.
9. Conversely sk-lem-sp-tower puts the total limit of any such tower in the exact
sfIntegralConstructible category used here, with the same completed coefficients.
10. Restrict the two functors using steps 8 and 9. The unit and counit isomorphisms
of steps 7 and 6 retain naturality and the triangular identities on these full
subcategories and give mutually inverse equivalences. -/
theorem sp_normalized_equivalence
    [∀ x : T, Invertible (l : T.residueField x)]
    (D : SpCoefficientTowersAbelian l E T) (R : SpReductionTower l E T D) :
    Nonempty (SpNormalizedEquivalence l E T D R) := by
  sorry

end AlgebraicGeometry.ProEtale
