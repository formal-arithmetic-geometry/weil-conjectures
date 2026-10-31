/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.DeligneLaumon.IntegralSupportNormalization.IntegralSupportNormalizationData
import all WeilConjectures.SmoothPurity.Sf.SfCompleteDirectImageReduction
import all WeilConjectures.CategoryTheory.SmoothPurity.CompactSupportIdentityCalculus
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleIdentifiedOpenClosed
import WeilConjectures.SmoothPurity.IntegralSupportNormalization.IntegralClosedReductionComparison
import WeilConjectures.SmoothPurity.IntegralSupportNormalization.IntegralClosedAlphaNormalization

/-! # Closed support comparison and normalized restricted adjunction

Source: smooth-purity localization support paragraphs; Stacks 03DI, 0GL1, 0A07
(blueprint: lem-sf-closed-support-normalization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] WeilConjectures.CompletedCoefficientPushforward.modAbelian
  WeilConjectures.CompletedCoefficientPushforward.hasDerived
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe u
open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures.IntegralSupportNormalization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

private theorem finiteClosed_interval {Z U X : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hcomplement : Set.range j = (Set.range i)ᶜ)
    (A : Type u) [CommRing A] (K : proEtaleDerivedCategory Z A) (a b : ℤ)
    (hK : proEtaleCohomologicalSupport K ⊆ Set.Icc a b) :
    proEtaleCohomologicalSupport ((proEtaleConstantDerivedDirectImage i A).obj K) ⊆
      Set.Icc a b := by
  let V : X.ProEt := ProEt.mk j
  have : IsOpenImmersion V.hom := inferInstanceAs (IsOpenImmersion j)
  have : QuasiCompact V.hom := inferInstanceAs (QuasiCompact j)
  obtain ⟨hlim, hcol, _⟩ := proEtaleIdentifiedOpenClosed i V hcomplement
    (proEtaleConstantRing X A) (proEtaleConstantRing Z A) (proEtaleConstantRing U A)
    (proEtaleConstantRingComparison i A) (proEtaleConstantRingComparison j A)
  have heq : proEtaleConstantRingPushforward A i =
      proEtaleConstantModuleDirectImage i A := by
    have hc : proEtaleRingDirectImageMap i (proEtaleConstantRing X A)
        (proEtaleConstantRing Z A) (asIso (proEtaleCoefficientInverseImageMap i A)) =
        proEtaleCoefficientDirectImageMap i A :=
      ((proEtaleSheafAdjunction i CommRingCat.{u + 1}).homEquiv _ _).apply_symm_apply _
    unfold proEtaleConstantRingPushforward proEtaleRingModuleDirectImage
      proEtaleConstantModuleDirectImage proEtaleConstantRingComparison
    rw [hc]
  change PreservesFiniteLimits (proEtaleConstantRingPushforward A i) at hlim
  change PreservesFiniteColimits (proEtaleConstantRingPushforward A i) at hcol
  rw [heq] at hlim hcol
  have : PreservesFiniteLimits (proEtaleConstantModuleDirectImage i A) := hlim
  have : PreservesFiniteColimits (proEtaleConstantModuleDirectImage i A) := hcol
  intro q hq
  apply hK
  intro hz
  let F := proEtaleConstantModuleDirectImage i A
  have hhom := (F.rightDerivedFunctorHomologyFunctorIso q).app K
  exact hq ((F.map_isZero hz).of_iso hhom.symm)

/-- Expand a composite shift square before specializing the coefficient functors. -/
private theorem compositeShiftSquare
    {C D B : Type*} [Category C] [Category D] [Category B]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift B ℤ]
    (F : C ⥤ D) (G : D ⥤ B) (H : C ⥤ B)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (α : F ⋙ G ⟶ H) (hα : NatTrans.CommShift α ℤ) (n : ℤ) (M : C) :
    (G.map ((F.commShiftIso n).hom.app M) ≫
      (G.commShiftIso n).hom.app (F.obj M)) ≫ (α.app M)⟦n⟧' =
        α.app (M⟦n⟧) ≫ (H.commShiftIso n).hom.app M := by
  let := hα
  simpa only [Functor.commShiftIso_comp_hom_app] using NatTrans.shift_app_comm α n M

/-- Restrict triangulatedness using the explicitly specified shift square. -/
private theorem triangulatedOfComp
    {C D B : Type*} [Category C] [Category D] [Category B]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift B ℤ]
    [HasZeroObject C] [HasZeroObject D] [HasZeroObject B]
    [Preadditive C] [Preadditive D] [Preadditive B]
    [∀ n : ℤ, (shiftFunctor C n).Additive]
    [∀ n : ℤ, (shiftFunctor D n).Additive]
    [∀ n : ℤ, (shiftFunctor B n).Additive]
    [Pretriangulated C] [Pretriangulated D] [Pretriangulated B]
    {F : C ⥤ D} {G : D ⥤ B} {H : C ⥤ B}
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    [G.Full] [G.Faithful] [G.IsTriangulated] [H.IsTriangulated]
    (e : F ⋙ G ≅ H) (h : NatTrans.CommShift e.hom ℤ) : F.IsTriangulated := by
  let := h
  exact (Functor.isTriangulated_iff_comp_right e).mpr inferInstance

/-- Whisker a specified shift square without searching for other shift structures. -/
private theorem whiskerShift
    {C D B : Type*} [Category C] [Category D] [Category B]
    [HasShift C ℤ] [HasShift D ℤ] [HasShift B ℤ]
    (F : C ⥤ D) (G H : D ⥤ B)
    [F.CommShift ℤ] [G.CommShift ℤ] [H.CommShift ℤ]
    (α : G ⟶ H) (h : NatTrans.CommShift α ℤ) :
    NatTrans.CommShift (whiskerLeft F α) ℤ := by
  let := h
  infer_instance

/-- The shift equation for an actual full-subcategory lift, with its maps unaltered. -/
private theorem liftedShiftInclusion
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    (P : ObjectProperty C) (Q : ObjectProperty D)
    [HasShift P.FullSubcategory ℤ] [HasShift Q.FullSubcategory ℤ]
    [P.ι.CommShift ℤ] [Q.ι.CommShift ℤ]
    (G : C ⥤ D) [G.CommShift ℤ]
    (hG : ∀ M : P.FullSubcategory, Q ((P.ι ⋙ G).obj M))
    (H : P.FullSubcategory ⥤ D) [H.CommShift ℤ]
    (s : (Q.lift (P.ι ⋙ G) hG).CommShift ℤ)
    (e : Q.lift (P.ι ⋙ G) hG ⋙ Q.ι ≅ H) (d : P.ι ⋙ G ≅ H)
    (h : e.hom = d.hom)
    (he : letI := s; NatTrans.CommShift e.hom ℤ)
    (hd : NatTrans.CommShift d.hom ℤ) :
    letI := s
    ∀ (n : ℤ) (M : P.FullSubcategory),
      (((Q.lift (P.ι ⋙ G) hG).commShiftIso n).hom.app M).hom ≫
        (Q.ι.commShiftIso n).hom.app ((Q.lift (P.ι ⋙ G) hG).obj M) =
      G.map ((P.ι.commShiftIso n).hom.app M) ≫ (G.commShiftIso n).hom.app M.obj := by
  let := s
  intro n M
  have h₁ := compositeShiftSquare (Q.lift (P.ι ⋙ G) hG) Q.ι H e.hom he n M
  have h₂ := compositeShiftSquare P.ι G H d.hom hd n M
  rw [h] at h₁
  simpa only [ObjectProperty.ι_map, ObjectProperty.ι_obj] using
    ((cancel_mono ((d.hom.app M)⟦n⟧')).mp (h₁.trans h₂.symm))

/-- The closed part of support normalization, with the original maps and shifts.
Source: smooth-purity localization, integral and rational support paragraphs
(blueprint: lem-sf-closed-support-normalization). -/
structure ClosedSupport (D : FiniteFieldDatum.{u}) (primeUnit : IsUnit (l : D.k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [i.IsOver (Spec (.of D.k))] [j.IsOver (Spec (.of D.k))] where
  closed : SfOrdinaryIntegralComparison l E i
  [closedReductionIso : IsIso (closedReduction l E i closed)]
  [closedModuleColimits : PreservesFiniteColimits (sfCompletedModuleDirectImage l E i)]
  [closedModuleLimits : PreservesFiniteLimits (sfCompletedModuleDirectImage l E i)]
  di : (sfIntegralConstructible l E Z).ι ⋙ FrobeniusExchange.integralDirectImage l E i ≅
    (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i
  di_formula : di.inv = closedAlpha l E i closed
  closedComplete : ∀ K : DerivedCategory (scalarReductionSource l E Z),
    IsSfDerivedComplete l E Z K →
      IsSfDerivedComplete l E X ((sfCompletedDerivedDirectImage l E i).obj K)
  closedInterval : ∀ (K : sfIntegralConstructibleCategory l E Z) (a b : ℤ),
    IntegralImmersionNormalization.HasReductionInterval l E Z K.obj a b →
    IntegralImmersionNormalization.HasReductionInterval l E X
      ((sfCompletedDerivedDirectImage l E i).obj K.obj) a b
  closedProjection : ∀ (K : sfIntegralConstructibleCategory l E Z) (n : ℕ),
    di.inv.app K ≫
      (coefficientSequenceProjection l E X n).app
        ((FrobeniusExchange.systemDirect l E i).obj
          ((FrobeniusExchange.reduction l E Z).obj K.obj)) =
    (sfCompletedDerivedDirectImage l E i).map
      (((FrobeniusExchange.models l E).system Z).adjunction.unit.app K.obj ≫
        (coefficientSequenceProjection l E Z n).app
          ((FrobeniusExchange.reduction l E Z).obj K.obj)) ≫
      (sfDerivedRestrictionComparison l E i n).hom.app
        ((coefficientSequenceDerivedEvaluation l E Z n).obj
          ((FrobeniusExchange.reduction l E Z).obj K.obj)) ≫
      (scalarReductionDerivedRestriction l E X n).map
        ((directEvaluationIso l E i n).inv.app
          ((FrobeniusExchange.reduction l E Z).obj K.obj))
  closedReductionComparison : ∀ (K : sfIntegralConstructibleCategory l E Z) (n : ℕ),
    IsIso (sfOrdinaryPushReduction l E i K.obj n)
  [closedShift : (FrobeniusExchange.directImageFunctor l E D.k primeUnit i).CommShift ℤ]
  closedShiftNormalization : NatTrans.CommShift di.hom ℤ
  closedShiftInclusion : ∀ (n : ℤ) (M : sfIntegralConstructibleCategory l E Z),
    (((FrobeniusExchange.directImageFunctor l E D.k primeUnit i).commShiftIso n).hom.app
      M).hom ≫ ((sfIntegralConstructible l E X).ι.commShiftIso n).hom.app
        ((FrobeniusExchange.directImageFunctor l E D.k primeUnit i).obj M) =
      (FrobeniusExchange.integralDirectImage l E i).map
        (((sfIntegralConstructible l E Z).ι.commShiftIso n).hom.app M) ≫
      ((FrobeniusExchange.integralDirectImage l E i).commShiftIso n).hom.app M.obj
  closedTermwiseShift : NatTrans.CommShift
    (isoWhiskerLeft (sfIntegralConstructible l E Z).ι
      (sfCompletedModuleDirectImage l E i).rightDerivedFunctorIsoMapDerivedCategory).hom ℤ
  closedExact : (FrobeniusExchange.directImageFunctor l E D.k primeUnit i).IsTriangulated
  disjoint : ∀ M : sfIntegralConstructibleCategory l E Z,
    IsZero ((constructibleIntegralPullback l E j).obj
      ((FrobeniusExchange.directImageFunctor l E D.k primeUnit i).obj M))

/-- Closed support comparison and normalized restricted adjunction.
Source: latest blueprint, prop-sf-open-closed-triangle-all-stages.proof.md,
integral and rational support paragraphs; Stacks 03DI, 03DJ, 0941, 099N, 0GL1, 0A07
(blueprint: lem-sf-closed-support-normalization).

Proof:
1. Obtain C from ordinary recollement. The ordinary module adjunction gives
   finite limits and the closed-kernel adjunction gives finite colimits. Use the
   normalized reduction-square theorem to make closedReduction invertible.
2. The reconstruction unit is invertible on constructible inputs. Its ordinary
   direct image followed by closedLimit is closedAlpha, hence invertible.
   Define di as its inverse. The strict comparison normalization supplies the
   projection formula and the prescribed shift equation.
3. Reuse completed_image_complete with C.diagrams. Choose the existing Roos
   presentation of actual integral direct image; C.push_reduction expresses
   each ordinary finite reduction map as a composite of two isomorphisms.
4. Identified-coefficient open/closed localization gives exact finite direct
   image. Its homology comparison preserves zero cohomology, hence every
   original reduction interval, including empty intervals. Transport through
   the preceding finite reduction isomorphisms.
5. Transport the ordinary derived shift through di and the fully faithful
   constructible inclusion. Cancel the typed restricted comparison against its
   normalized ambient square to obtain the stated inclusion equation.
   Triangulatedness restricts through the same comparison. The universal-unit
   termwise comparison respects shifts.
6. R.disjoint gives vanishing on the ordinary closed image. Transport along
   di under actual open pullback and reflect the zero identity through the
   faithful constructible inclusion. -/
theorem closedSupportNormalization (D : FiniteFieldDatum.{u}) (primeUnit : IsUnit (l : D.k))
    {Z U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [Z.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (Z ↘ Spec (.of D.k))] [QuasiCompact (Z ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    [∀ x : Z, Invertible (l : Z.residueField x)]
    (i : Z ⟶ X) [IsClosedImmersion i]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] [i.IsOver (Spec (.of D.k))]
    (_hcomplement : Set.range j = (Set.range i)ᶜ) :
    Nonempty (ClosedSupport l E D primeUnit i j) := by
  obtain ⟨R⟩ := sfIntegralOrdinaryRecollement_realization l E D.k primeUnit
    (X ↘ Spec (.of D.k)) i j _hcomplement
  let C := R.closed
  let : PreservesFiniteLimits (sfCompletedModuleDirectImage l E i) := by
    let : PreservesLimits (sfCompletedModuleDirectImage l E i) :=
      (sfOrdinaryModuleAdjunction l E i).rightAdjoint_preservesLimits
    infer_instance
  let : PreservesFiniteColimits (sfCompletedModuleDirectImage l E i) := by
    let : PreservesColimits (sfCompletedModuleDirectImage l E i) :=
      R.kernelAdjunction.leftAdjoint_preservesColimits
    infer_instance
  have hr : IsIso (closedReduction l E i C) := closedReduction_isIso l E i C
  let := hr
  have ha : IsIso (closedAlpha l E i C) := by
    have hu (K : sfIntegralConstructibleCategory l E Z) :
        IsIso ((((FrobeniusExchange.models l E).system Z).adjunction.unit).app K.obj) :=
      (FrobeniusExchange.models l E).complete Z K
    have h (K : sfIntegralConstructibleCategory l E Z) :
        IsIso ((closedAlpha l E i C).app K) := by
      change IsIso ((sfCompletedDerivedDirectImage l E i).map
        (((FrobeniusExchange.models l E).system Z).adjunction.unit.app K.obj) ≫
          (closedLimit l E i C).hom.app ((FrobeniusExchange.reduction l E Z).obj K.obj))
      refine IsIso.comp_isIso' ?_ ?_
      · exact @Functor.map_isIso _ _ _ _ _ _ _ _ (hu K)
      · exact ((closedLimit l E i C).app
          ((FrobeniusExchange.reduction l E Z).obj K.obj)).isIso_hom
    exact NatIso.isIso_of_isIso_app _
  let d := (asIso (closedAlpha l E i C)).symm
  let e : FrobeniusExchange.directImageFunctor l E D.k primeUnit i ⋙
        (sfIntegralConstructible l E X).ι ≅
      (sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i := d
  let sc := Functor.CommShift.ofComp e ℤ
  let := sc
  have hcompat : NatTrans.CommShift e.hom ℤ := Functor.CommShift.ofComp_compatibility e ℤ
  have hα := closedAlpha_normalization l E i C
  have hs : NatTrans.CommShift d.hom ℤ := by
    have := hα.1
    exact NatTrans.CommShift.of_isIso (closedAlpha l E i C) ℤ
  have he : (FrobeniusExchange.directImageFunctor l E D.k primeUnit i).IsTriangulated := by
    exact triangulatedOfComp e hcompat
  have hred (K : sfIntegralConstructibleCategory l E Z) (n : ℕ) :
      IsIso (sfOrdinaryPushReduction l E i K.obj n) := by
    obtain ⟨hp, L, hL⟩ := FrobeniusExchange.directImage_roos l E D.k primeUnit i K
    let := hp
    have h := C.push_reduction K.obj K.property L n
    rw [← h.2]
    refine IsIso.comp_isIso' ?_ h.1
    exact @Functor.map_isIso _ _ _ _ _ _ _ _ (C.push K.obj K.property L).isIso_hom
  refine ⟨{
    closed := C
    closedReductionIso := hr
    closedModuleColimits := inferInstance
    closedModuleLimits := inferInstance
    di := d
    di_formula := rfl
    closedComplete := fun K hK ↦ completed_image_complete l E i C.diagrams K hK
    closedInterval := by
      intro K a b hK n q hq
      have := hred K n
      let e := asIso (sfOrdinaryPushReduction l E i K.obj n)
      have ht := finiteClosed_interval i j _hcomplement
        (Padic.coefficientExtensionRing l E (n + 1))
        ((scalarReductionDerivedExtension l E Z n).obj K.obj) a b (hK n)
      exact ht (fun hz ↦ hq
        (((DerivedCategory.homologyFunctor _ q).mapIso e).isZero_iff.mpr hz))
    closedProjection := hα.2
    closedReductionComparison := hred
    closedShift := sc
    closedShiftNormalization := hs
    closedShiftInclusion := by
      unfold FrobeniusExchange.directImageFunctor
      exact liftedShiftInclusion (sfIntegralConstructible l E Z)
        (sfIntegralConstructible l E X) (FrobeniusExchange.integralDirectImage l E i)
        (FrobeniusExchange.directImage_constructible l E D.k primeUnit i)
        ((sfIntegralConstructible l E Z).ι ⋙ sfCompletedDerivedDirectImage l E i)
        sc e d rfl hcompat hs
    closedTermwiseShift := ?_
    closedExact := he
    disjoint := ?_ }⟩
  · exact whiskerShift (sfIntegralConstructible l E Z).ι _ _
      (sfCompletedModuleDirectImage l E i).rightDerivedFunctorIsoMapDerivedCategory.hom
      (rightExactIso_shift (sfCompletedModuleDirectImage l E i))
  · intro M
    let P := (C.pushFunctor l E i).obj M
    have hz := R.disjoint M
    rw [IsZero.iff_id_eq_zero] at hz ⊢
    apply (sfIntegralConstructible l E U).ι.map_injective
    change 𝟙 ((integralDerivedPullback l E j).obj
      ((FrobeniusExchange.integralDirectImage l E i).obj M.obj)) = 0
    have hordinary : IsZero ((integralDerivedPullback l E j).obj P.obj) := by
      rw [IsZero.iff_id_eq_zero]
      exact congrArg (fun f ↦ f.hom) hz
    exact ((integralDerivedPullback l E j).mapIso (d.app M)).isZero_iff.mpr
      hordinary |>.eq_of_src _ _

end WeilConjectures.IntegralSupportNormalization
