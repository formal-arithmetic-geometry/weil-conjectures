/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.AlgebraicGeometry.CompletedIntegralConstantMapOfUniverses
public import WeilConjectures.SmoothPurity.Completed.CompletedIntegralCoefficientGerm
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructible
public import WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafOperations
public import WeilConjectures.SmoothPurity.IntegralImmersionNormalization.IntegralImmersionPullbackNormalization
public import WeilConjectures.SmoothPurity.Qcqs.QcqsCompactSupportRealization
public import WeilConjectures.SmoothPurity.Sf.SfDerivedDirectImage
public import WeilConjectures.SmoothPurity.Derived.DerivedScalarExtensionRestrictionAdjunctionSupplement
public import WeilConjectures.SixFunctors.FrobeniusExchange.SystemOperationExchangeRealization
public import WeilConjectures.SmoothPurity.Sf.SfIntegralOrdinaryRecollementRealization
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory

public import WeilConjectures.DeligneLaumon.IntegralSupportNormalization.IntegralSupportNormalizationData
import WeilConjectures.SmoothPurity.IntegralSupportNormalization.IntegralOpenSupportNormalization
import WeilConjectures.SmoothPurity.IntegralSupportNormalization.IntegralClosedSupportNormalization
import WeilConjectures.SmoothPurity.Supporting.DirectImagesConstructible
import WeilConjectures.SmoothPurity.Sf.SfIntegralConstructibleTriangulated
import WeilConjectures.ZetaSeries

/-! # Assembly of normalized integral support operations

Source: smooth-purity localization support paragraphs
(blueprint: lem-sf-integral-support-functor-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSupportNormalization

private theorem cancel_inverse {C : Type*} [Category C] {A B P T : C}
    (e : B ≅ T) (f : A ⟶ B) (g : A ⟶ P) (q : P ⟶ T)
    (h : f = g ≫ q ≫ e.inv) : f ≫ e.hom = g ≫ q := by
  rw [h]
  simp only [Category.assoc, e.inv_hom_id, Category.comp_id]

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- Normalized integral support functors and their restricted adjunctions.
Source: latest blueprint, prop-sf-open-closed-triangle-all-stages.proof.md, integral
and rational support paragraphs; Stacks 09AA, 09BM, 09BN, 0GL1, 0A07, 04C4 and 095R
(blueprint: lem-sf-integral-support-functor-normalization).

Proof:
1. Apply integral-immersion-pullback-normalization: X,U,Z are Noetherian qcqs,
   j is quasi-compact, the coefficient quotients are finite perfect, and the
   ordinary pullback comparisons retain constants, quotient projections and shifts.
   Ringed open-closed localization gives exact ordinary j! and i*, their adjunctions,
   and j* i*=0; closed exactness uses the retrocompact open complement.
2. Apply integral-open-reduction-comparison. The strict system isomorphism r and
   the actual reduction/limit unit give d = L(r inverse) followed by the inverse unit.
   For (j,id), the published compact-support realization is this same map. Its finite
   projections are the tensor comparisons. Remove the proper identity by its
   section-normalized comparison. The strict-system unit/counit equations descend
   to exactly openSystemUnit and openSystemCounit.
3. Ordinary closed image commutes with scalar restriction sectionwise: both evaluate
   on V times_X Z with the identical coefficient action. Its limit comparison is
   the conjugate of the ordinary inverse-image/quotient square. Compose it with image
   of the actual completion unit to get closedAlpha; define di as its inverse.
   Direct-image-limits and Koszul reconstruction give completeness and invertibility.
   Naturality and the projection equations hold for whole strict towers, before
   separate evaluation; no faithfulness of derived evaluation is asserted.
4. Open finite-constructibility-interval keeps each reduction in the original [a,b].
   For the closed case use constructible pro-etale origin, exact site comparison,
   comparison of finite closed image, and exact constructible etale closed image.
   Induction with truncation triangles identifies cohomology as the image of input
   cohomology. Hence the same interval works at every level. The actual reductions
   and completeness put both ordinary images in the recorded integral category.
5. On complexes exact open extension, closed image and scalar restriction commute
   with the shifted differential. Quotient augmentations have their actual quotient
   projections and zero second Roos coordinate. The signed cone shift commutes with
   these maps, giving the displayed shift compatibility for dj and di; the closed
   right-derived/termwise comparison is normalized by its universal unit.
6. Exact termwise functors are triangulated and constant-section R-linear. Restrict
   to the full constructible subcategories and transport through dj and di. This
   gives exact R-linear support functors with precisely these termwise shifts.
7. Derive the ordinary module adjunctions and restrict along the full inclusions.
   The fully-faithful restriction formulas give openUnit, openCounit, closedUnit,
   closedCounit and the triangle identities. Step 2 identifies the open maps with
   strict-system realization. Finally j* i*=0 on complexes, so the normalized
   comparisons give the stated zero composite of the actual integral functors. -/
theorem integralSupportFunctorNormalization (D : FiniteFieldDatum.{u}) (_hl : l ≠ D.p)
    {Z U X : Scheme.{u}} [X.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    (i : Z ⟶ X) (j : U ⟶ X) [IsClosedImmersion i] [IsOpenImmersion j]
    (_hcomplement : Set.range j = (Set.range i)ᶜ) :
    Nonempty (Normalization l E D i j) := by
  let hunit : IsUnit (l : D.k) := finiteFieldDatumPrimeUnit D l _hl
  obtain ⟨hX, hU, hZ, _, _, _, hj, _, _, _⟩ :=
    IntegralImmersionNormalization.integralImmersionPullbackNormalization l E D _hl
      X U Z (X ↘ Spec (.of D.k)) i j _hcomplement
  let := hX
  let := hU
  let := hZ
  let := hj
  let : U.Over (Spec (.of D.k)) := ⟨j ≫ X ↘ Spec (.of D.k)⟩
  let : Z.Over (Spec (.of D.k)) := ⟨i ≫ X ↘ Spec (.of D.k)⟩
  let : j.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  let : i.IsOver (Spec (.of D.k)) := ⟨rfl⟩
  let : LocallyOfFiniteType (U ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (j ≫ X ↘ Spec (.of D.k)))
  let : LocallyOfFiniteType (Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (LocallyOfFiniteType (i ≫ X ↘ Spec (.of D.k)))
  let : QuasiCompact (U ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (j ≫ X ↘ Spec (.of D.k)))
  let : QuasiCompact (Z ↘ Spec (.of D.k)) :=
    inferInstanceAs (QuasiCompact (i ≫ X ↘ Spec (.of D.k)))
  let : ∀ x : X, Invertible (l : X.residueField x) := fun x ↦
    (by simpa using hunit.map ((X ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
      IsUnit (l : X.residueField x)).invertible
  let : ∀ x : U, Invertible (l : U.residueField x) := fun x ↦
    (by simpa using hunit.map ((U ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
      IsUnit (l : U.residueField x)).invertible
  let : ∀ x : Z, Invertible (l : Z.residueField x) := fun x ↦
    (by simpa using hunit.map ((Z ↘ Spec (.of D.k)).residueFieldAlgebraMap x) :
      IsUnit (l : Z.residueField x)).invertible
  obtain ⟨O⟩ := openSupportNormalization l E D hunit j
  obtain ⟨C⟩ := closedSupportNormalization l E D hunit i j _hcomplement
  let := C.closedReductionIso
  let := C.closedModuleColimits
  let := C.closedModuleLimits
  let := O.openShift
  let := C.closedShift
  let τ := whiskerLeft (sfIntegralConstructible l E X).ι C.closed.pull
  have : ∀ K : sfIntegralConstructibleCategory l E X, IsIso (τ.app K) := fun K ↦
    C.closed.pull_complete K.obj K.property.1
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  let pi : constructibleIntegralPullback l E i ⋙ (sfIntegralConstructible l E Z).ι ≅
      (sfIntegralConstructible l E X).ι ⋙ sfOrdinaryDerivedPull l E i := (asIso τ).symm
  let ai : constructibleIntegralPullback l E i ⊣
      FrobeniusExchange.directImageFunctor l E D.k hunit i :=
    (sfOrdinaryDerivedAdjunction l E i).restrictFullyFaithful
    (sfIntegralConstructible l E X).fullyFaithfulι
    (sfIntegralConstructible l E Z).fullyFaithfulι pi.symm C.di.symm
  refine ⟨{
    primeUnit := hunit
    closed := C.closed
    closedReductionIso := C.closedReductionIso
    closedModuleColimits := C.closedModuleColimits
    closedModuleLimits := C.closedModuleLimits
    dj := O.dj
    dj_formula := O.dj_formula
    di := C.di
    di_formula := C.di_formula
    openPull := O.openPull
    closedPull := pi
    closedPull_formula := ?_
    openComplete := O.openComplete
    closedComplete := C.closedComplete
    openConstructible := ?_
    closedConstructible := ?_
    openInterval := O.openInterval
    closedInterval := C.closedInterval
    openReduction := O.openReduction
    openProjection := O.openProjection
    closedProjection := C.closedProjection
    closedReductionComparison := C.closedReductionComparison
    openAdjunction := O.openAdjunction
    closedAdjunction := ai
    openUnit := ?_
    openCounit := ?_
    closedUnit := ?_
    closedCounit := ?_
    openSystemUnit := O.openSystemUnit
    openSystemCounit := O.openSystemCounit
    openShift := O.openShift
    closedShift := C.closedShift
    openShiftNormalization := O.openShiftNormalization
    closedShiftNormalization := C.closedShiftNormalization
    closedShiftInclusion := C.closedShiftInclusion
    closedTermwiseShift := C.closedTermwiseShift
    openExact := O.openExact
    closedExact := C.closedExact
    openLinear := (sfCompactSupportFiniteIntegralFunctor_linear l D.k hunit
      (Compactification.ofIsOpenImmersion j) E).2
    closedLinear := (FrobeniusExchange.directImage_linear l E D.k hunit i).2
    disjoint := C.disjoint }⟩
  · intro K
    exact (asIso τ).inv_hom_id_app K
  · intro K
    exact ObjectProperty.prop_of_iso (sfIntegralConstructible l E X) (O.dj.app K)
      ((sfCompactSupportFiniteIntegralFunctor l D.k hunit
        (Compactification.ofIsOpenImmersion j) E).obj K).property
  · intro K
    exact ObjectProperty.prop_of_iso (sfIntegralConstructible l E X) (C.di.app K)
      ((FrobeniusExchange.directImageFunctor l E D.k hunit i).obj K).property
  · intro N
    rw [O.openAdjunction_formula]
    have h := (ordinaryOpenAdjunction l E j).map_restrictFullyFaithful_unit_app
      (L := sfCompactSupportFiniteIntegralFunctor l D.k hunit
        (Compactification.ofIsOpenImmersion j) E) (R := constructibleIntegralPullback l E j)
      (sfIntegralConstructible l E U).fullyFaithfulι
      (sfIntegralConstructible l E X).fullyFaithfulι O.dj.symm O.openPull.symm N
    exact cancel_inverse (O.openPull.app
      ((sfCompactSupportFiniteIntegralFunctor l D.k hunit
        (Compactification.ofIsOpenImmersion j) E).obj N)) _ _ _ h
  · intro K
    rw [O.openAdjunction_formula]
    exact (ordinaryOpenAdjunction l E j).map_restrictFullyFaithful_counit_app
      (sfIntegralConstructible l E U).fullyFaithfulι
      (sfIntegralConstructible l E X).fullyFaithfulι O.dj.symm O.openPull.symm K
  · intro K
    have h := (sfOrdinaryDerivedAdjunction l E i).map_restrictFullyFaithful_unit_app
      (L := constructibleIntegralPullback l E i)
      (R := FrobeniusExchange.directImageFunctor l E D.k hunit i)
      (sfIntegralConstructible l E X).fullyFaithfulι
      (sfIntegralConstructible l E Z).fullyFaithfulι pi.symm C.di.symm K
    exact cancel_inverse (C.di.app ((constructibleIntegralPullback l E i).obj K)) _ _ _ h
  · intro M
    exact (sfOrdinaryDerivedAdjunction l E i).map_restrictFullyFaithful_counit_app
      (L := constructibleIntegralPullback l E i)
      (R := FrobeniusExchange.directImageFunctor l E D.k hunit i)
      (sfIntegralConstructible l E X).fullyFaithfulι
      (sfIntegralConstructible l E Z).fullyFaithfulι pi.symm C.di.symm M

end WeilConjectures.IntegralSupportNormalization
