/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.CoefDerivedSystemEvaluationCalculus
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Sheaf.Paper.DerivedAdjunctionShift
import Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit

public import Sheaf.Algebra.Homology.KFlatIndependentCoefficients
import Sheaf.Algebra.Homology.KInjectiveProductsTermwise
import Sheaf.CategoryTheory.ExactFunctorDerivedFunctor
import Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction
import Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses
import Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition
import Sheaf.Paper.CoefficientRingedSequenceSite
import Sheaf.Paper.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.RoosSplitComparison
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
/-!
# Shift compatibility of the coefficient reduction/limit adjunction

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
`sk-thm-sf-package/fix-prop-coherence.proof.md`, coefficient-comparison sentence
(blueprint: lem-pur-reduction-limit-shift-adjunction).

The finite K-flat comparison fixes the reduction shift. The actual resolution
comparison fixes the limit shift on every K-injective replacement, including
`j[r]`. The Roos triangles below have this very limit as their first vertex;
their connecting maps satisfy the signed shift equation for that comparison.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option warn.sorry false
set_option synthInstance.maxSize 2048

-- Use the existing coefficient-universe sheafification on the small site.
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace WeilConjectures

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (W : Scheme.{t})

/-- The canonical comparison from the actual sequence limit to the termwise
limit of a specified K-injective replacement of the restricted sequence.
It is the exact restriction/localization comparison, followed by `Rlim(j)` and
`rightDerivedFunctorObjQIso`; no new choice of a derived functor is made.
Source: Stacks 0941 and 0D6E
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
def purCoefficientLimitModel
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j] :
    (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N) ≅
      DerivedCategory.Q.obj (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
        scalarReductionSource l E W).mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
  (coefficientConstantTowerLimit l E W).mapIso
      ((coefficientSequenceRestriction l E W).mapDerivedCategoryFactors.app N ≪≫
        asIso (DerivedCategory.Q.map j)) ≪≫
    Functor.rightDerivedFunctorObjQIso
      (lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤ scalarReductionSource l E W) I

/-- The shifted replacement map is exactly `j[r]`, with the canonical termwise
identification `U(N[r]) ≅ (UN)[r]` in its source.
Source: Stacks 0941, derived.tex 070H
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
def purCoefficientShiftedResolution
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ I) (r : ℤ) :
    ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (N⟦r⟧) ⟶ I⟦r⟧ :=
  (((coefficientSequenceRestriction l E W).mapHomologicalComplex
    (ComplexShape.up ℤ)).commShiftIso r).hom.app N ≫ j⟦r⟧'

/-- The canonical product comparison for the evaluated shifted tower, using
localization's cochain shift and preservation of products by the shift equivalence.
Source: Stacks 0941 and derived.tex 0BK6
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
def purCoefficientRoosProductShift
    [HasCountableProducts (DerivedCategory (scalarReductionSource l E W))]
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ) (r : ℤ) :
    (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj ((I⟦r⟧).asFunctor.obj (op n))) ≅
      (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n)))⟦r⟧ :=
  Limits.Pi.mapIso (fun n : ℕ ↦ (DerivedCategory.Q.commShiftIso r).app
    (I.asFunctor.obj (op n))) ≪≫
      (PreservesProduct.iso (shiftFunctor _ r)
        (fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n)))).symm

/-- A Roos triangle whose first vertex is the actual sequence-limit functor,
computed on a specified simultaneous K-injective tower. Its first arrow is
normalized by the actual limit-cone projections through `purCoefficientLimitModel`.
Source: Stacks 0941 and 08TC
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
structure PurCoefficientRoosTriangle
    [HasCountableProducts (DerivedCategory (scalarReductionSource l E W))]
    (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
    (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
    (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j] where
  p : (coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N) ⟶
    ∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n))
  δ : (∏ᶜ fun n : ℕ ↦ DerivedCategory.Q.obj (I.asFunctor.obj (op n))) ⟶
    ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N))⟦(1 : ℤ)⟧
  triangle : IsDerivedLimitTriangle
    (fun n : ℕ ↦ DerivedCategory.Q.map
      (I.asFunctor.map (homOfLE (Nat.le_succ n)).op))
    ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N)) p δ
  projection : ∀ n : ℕ,
    p ≫ Limits.Pi.π _ n = (purCoefficientLimitModel l E W N I j).hom ≫
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex
        (lim.π (op n)) (ComplexShape.up ℤ)).app I)

/-- Normalized shifts for the given reduction/limit adjunction. Finite shifts
are fixed by the existing K-flat model, not chosen to match reduction afterwards.
The limit equation uses the fixed resolution comparison for `j` and `j[r]`.
The Roos connecting-map equation uses that same `limit_shift` and the actual
limit triangles, with the cochain sign `r.negOnePow`.
Source: Stacks 07A6, 0941 and derived.tex 0A8D
(blueprint: lem-pur-reduction-limit-shift-adjunction). -/
structure PurReductionLimitShiftData
    (S : CoefficientDerivedSystemCalculus l E W) where
  reduction_shift : S.reduction.CommShift ℤ
  finite_reduction_shift :
    ∀ n : ℕ, (coefficientFiniteDerivedExtension l E W n).CommShift ℤ
  finite_shift_model :
    ∀ (n : ℕ) (Q : CochainComplex (scalarReductionSource l E W) ℤ) (r : ℤ)
      (hQ : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W) Q)
      (hQr : CochainComplex.IsKFlatIndependentCoefficients
        (J := Scheme.ProEt.topology W) (R := completedIntegralCommRingSheafUnrestricted l E W)
          (Q⟦r⟧)),
      letI := finite_reduction_shift n
      (coefficientFiniteDerivedExtension l E W n).map
          ((DerivedCategory.Q.commShiftIso r).hom.app Q) ≫
        ((coefficientFiniteDerivedExtension l E W n).commShiftIso r).hom.app
          (DerivedCategory.Q.obj Q) ≫
        (coefficientFiniteReductionModel l E W Q hQ n).hom⟦r⟧' =
      (coefficientFiniteReductionModel l E W (Q⟦r⟧) hQr n).hom ≫
        DerivedCategory.Q.map
          ((((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).commShiftIso r).hom.app Q) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          (((scalarReductionExtension l E W n).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj Q)
  reduction_shift_evaluation :
    ∀ n : ℕ,
      letI := reduction_shift
      letI := finite_reduction_shift n
      NatTrans.CommShift (S.reductionEvaluation n).hom ℤ
  limit_shift : (coefficientSequenceLimit l E W).CommShift ℤ
  limit_shift_resolution :
    ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j]
      (r : ℤ) [(I⟦r⟧).IsKInjective]
      [QuasiIso (purCoefficientShiftedResolution l E W N I j r)],
      letI := limit_shift
      (coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
        ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
          (DerivedCategory.Q.obj N) ≫
        (purCoefficientLimitModel l E W N I j).hom⟦r⟧' =
      (purCoefficientLimitModel l E W (N⟦r⟧) (I⟦r⟧)
        (purCoefficientShiftedResolution l E W N I j r)).hom ≫
        DerivedCategory.Q.map
          ((((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
            scalarReductionSource l E W).mapHomologicalComplex
              (ComplexShape.up ℤ)).commShiftIso r).hom.app I) ≫
        (DerivedCategory.Q.commShiftIso r).hom.app
          (((lim : (ℕᵒᵖ ⥤ scalarReductionSource l E W) ⥤
            scalarReductionSource l E W).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj I)
  products : HasCountableProducts (DerivedCategory (scalarReductionSource l E W))
  roos :
    letI := products
    ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j],
      PurCoefficientRoosTriangle l E W N I j
  roos_triangle_shift :
    letI := products
    letI := limit_shift
    ∀ (N : CochainComplex (coefficientSequenceModules l E W) ℤ)
      (I : CochainComplex (ℕᵒᵖ ⥤ scalarReductionSource l E W) ℤ)
      (j : ((coefficientSequenceRestriction l E W).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj N ⟶ I) [I.IsKInjective] [QuasiIso j]
      (r : ℤ) [(I⟦r⟧).IsKInjective]
      [QuasiIso (purCoefficientShiftedResolution l E W N I j r)],
      ((roos (N⟦r⟧) (I⟦r⟧) (purCoefficientShiftedResolution l E W N I j r)).p ≫
        (purCoefficientRoosProductShift l E W I r).hom =
      (coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
        ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
          (DerivedCategory.Q.obj N) ≫ (roos N I j).p⟦r⟧') ∧
      ((roos (N⟦r⟧) (I⟦r⟧) (purCoefficientShiftedResolution l E W N I j r)).δ ≫
        ((coefficientSequenceLimit l E W).map
          ((DerivedCategory.Q.commShiftIso r).hom.app N) ≫
          ((coefficientSequenceLimit l E W).commShiftIso r).hom.app
            (DerivedCategory.Q.obj N))⟦(1 : ℤ)⟧' =
      r.negOnePow • ((purCoefficientRoosProductShift l E W I r).hom ≫
        (roos N I j).δ⟦r⟧' ≫ (shiftFunctorComm _ 1 r).hom.app
          ((coefficientSequenceLimit l E W).obj (DerivedCategory.Q.obj N))))
  unit_shift :
    letI := reduction_shift
    letI := limit_shift
    ∀ r : ℤ,
      Adjunction.CommShift.CompatibilityUnit S.adjunction
        (S.reduction.commShiftIso r)
        ((coefficientSequenceLimit l E W).commShiftIso r)
  counit_shift :
    letI := reduction_shift
    letI := limit_shift
    ∀ r : ℤ,
      Adjunction.CommShift.CompatibilityCounit S.adjunction
        (S.reduction.commShiftIso r)
        ((coefficientSequenceLimit l E W).commShiftIso r)

/-- Every supplied coherent coefficient calculus admits the prescribed termwise
shift comparisons, with its actual unit and counit.

Source: literature/blueprint/main-20261015/blueprint/sec-six-functors/
`sk-thm-sf-package/fix-prop-coherence.proof.md`, coefficient-comparison sentence
(blueprint: lem-pur-reduction-limit-shift-adjunction).

Proof:
1. Regard strict systems as modules on the simultaneous sequence site and use
   its ordinary tensor/direct-image adjunction (def-coef-ringed-sequence-site).
2. Derive pullback on flat-term K-flat representatives. Termwise cochain shift
   is the identity on the shifted tensor terms, with differential (-1)^r d.
   The universal finite counits give `finite_shift_model`. The simultaneous
   K-flat reduction model gives the evaluated shift equation for S.reduction.
3. Factor direct image as exact restriction followed by limit. The canonical
   composition comparison is `purCoefficientLimitModel`. For a K-injective
   replacement j use j[r]; termwise limit gives lim(j[r]) = (lim j)[r].
   K-injective shift stability and invariance of quasi-isomorphisms supply all
   the shifted-resolution instances in the displayed universal equations.
4. The ringed strict-tower homotopy-limit theorem supplies the Roos triangles
   for this actual limit, with the specified limit-cone projections. Injective
   tower transitions split, so the kernel-to-shifted-cone comparison is a
   quasi-isomorphism. On Cone(1-s)[-1], the map (y,x) ↦ ((-1)^r y,x)
   intertwines the shift differentials and fixes the kernel inclusion (0,x).
   It gives the two Roos shift equations, including the connecting-map sign.
5. Apply lem-weil-pbc-derived-adjunction-shift to the canonical derived
   adjunction of step 1. Steps 2 and 3 identify its resolution comparisons
   with the ones specified here. This gives both unit and counit equations
   as system transformations, before evaluation, for every integer shift.
6. At r=0 the comparisons are identities; at r=1 and -1 the first cone
   coordinate is negated. Signs multiply for repeated shifts. Zero complexes,
   degree-zero sheaves and the empty scheme require no additional hypothesis.
-/
theorem purReductionLimitShiftAdjunction
    (S : CoefficientDerivedSystemCalculus l E W)
    (hS : CoefficientDerivedSystemCoherence l E W S) :
    Nonempty (PurReductionLimitShiftData l E W S) := by
  sorry

end WeilConjectures
