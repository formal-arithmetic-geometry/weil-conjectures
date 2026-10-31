/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralSupportNormalizationData
import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportFiniteComparison
import WeilConjectures.AlgebraicGeometry.IntegralOpenAdjunctionTransposeNormalization
import all WeilConjectures.AlgebraicGeometry.SfIntegralCompactSupportConstructible
import all WeilConjectures.AlgebraicGeometry.SfCompleteDirectImageReduction
import WeilConjectures.SixFunctors.OpenQuotientKoszulCompleteness
import WeilConjectures.SixFunctors.OpenDvrRingedIdentification

import WeilConjectures.AlgebraicGeometry.QcqsCompactSupportRealization

/-! # Open support comparison and strict-system adjunction maps

Source: smooth-purity localization support paragraphs; Stacks 03DI, 0GL1, 0A07
(blueprint: lem-sf-open-support-normalization).
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

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

/-- The open part of support normalization, with the original maps and shifts.
Source: smooth-purity localization, integral and rational support paragraphs
(blueprint: lem-sf-open-support-normalization). -/
structure OpenSupport (D : FiniteFieldDatum.{u}) (primeUnit : IsUnit (l : D.k))
    {U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] where
  dj : sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E ⋙ (sfIntegralConstructible l E X).ι ≅
    (sfIntegralConstructible l E U).ι ⋙ ordinaryOpen l E j
  dj_formula : dj = (sfQcqsCompactSupportRealization l E D.k primeUnit
      (Compactification.ofIsOpenImmersion j)).symm ≪≫
    isoWhiskerLeft (sfIntegralConstructible l E U).ι (openIdentity l E j)
  openPull : constructibleIntegralPullback l E j ⋙ (sfIntegralConstructible l E U).ι ≅
    (sfIntegralConstructible l E X).ι ⋙ ordinaryOpenPull l E j
  openComplete : ∀ K : DerivedCategory (scalarReductionSource l E U),
    IsSfDerivedComplete l E U K → IsSfDerivedComplete l E X ((ordinaryOpen l E j).obj K)
  openInterval : ∀ (K : sfIntegralConstructibleCategory l E U) (a b : ℤ),
    IntegralImmersionNormalization.HasReductionInterval l E U K.obj a b →
    IntegralImmersionNormalization.HasReductionInterval l E X
      ((ordinaryOpen l E j).obj K.obj) a b
  openReduction : ∀ n : ℕ,
    (sfIntegralConstructible l E U).ι ⋙ ordinaryOpen l E j ⋙
        scalarReductionDerivedExtension l E X n ≅
      (sfIntegralConstructible l E U).ι ⋙ scalarReductionDerivedExtension l E U n ⋙
        sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n+1))
          (Compactification.ofIsOpenImmersion j)
  openProjection : ∀ (K : sfIntegralConstructibleCategory l E U) (n : ℕ),
    (scalarReductionDerivedExtension l E X n).map (dj.hom.app K) ≫
      (openReduction n).hom.app K =
    (sfCompactSupportFiniteReductionIso l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E K n).hom
  openAdjunction : sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E ⊣ constructibleIntegralPullback l E j
  openAdjunction_formula : openAdjunction =
    (ordinaryOpenAdjunction l E j).restrictFullyFaithful
      (sfIntegralConstructible l E U).fullyFaithfulι
      (sfIntegralConstructible l E X).fullyFaithfulι dj.symm openPull.symm
  openSystemUnit : ∀ N : sfIntegralConstructibleCategory l E U,
    (FrobeniusExchange.reduction l E U).map (openAdjunction.unit.app N).hom ≫
      (integralComparisonPullbackCounit l E j
        ((FrobeniusExchange.models l E).system X)
        ((FrobeniusExchange.models l E).system U)
        ((FrobeniusExchange.models l E).roos U)
        ((FrobeniusExchange.models l E).pullback j)).app
          (((sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
            (Compactification.ofIsOpenImmersion j) E).obj N).obj) ≫
      (integralComparisonDerivedSequencePullback l E j).map
        ((FrobeniusExchange.compactOperationReduction l E D.k primeUnit j
          (Compactification.ofIsOpenImmersion j)).app N ≫
          (systemDirectId l E X).hom.app
            ((FrobeniusExchange.systemDerivedOpen l E j).obj
              ((FrobeniusExchange.reduction l E U).obj N.obj))) =
    (FrobeniusExchange.systemDerivedOpenAdjunction l E j).unit.app
      ((FrobeniusExchange.reduction l E U).obj N.obj)
  openSystemCounit : ∀ K : sfIntegralConstructibleCategory l E X,
    (FrobeniusExchange.reduction l E X).map (openAdjunction.counit.app K).hom =
      ((FrobeniusExchange.compactOperationReduction l E D.k primeUnit j
        (Compactification.ofIsOpenImmersion j)).app
          ((constructibleIntegralPullback l E j).obj K)) ≫
      (systemDirectId l E X).hom.app
        ((FrobeniusExchange.systemDerivedOpen l E j).obj
          ((FrobeniusExchange.reduction l E U).obj
            ((constructibleIntegralPullback l E j).obj K).obj)) ≫
      (FrobeniusExchange.systemDerivedOpen l E j).map
        ((integralComparisonPullbackCounit l E j
          ((FrobeniusExchange.models l E).system X)
          ((FrobeniusExchange.models l E).system U)
          ((FrobeniusExchange.models l E).roos U)
          ((FrobeniusExchange.models l E).pullback j)).app K.obj) ≫
      (FrobeniusExchange.systemDerivedOpenAdjunction l E j).counit.app
        ((FrobeniusExchange.reduction l E X).obj K.obj)
  [openShift : (sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
    (Compactification.ofIsOpenImmersion j) E).CommShift ℤ]
  openShiftNormalization : NatTrans.CommShift dj.hom ℤ
  openExact : (sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
    (Compactification.ofIsOpenImmersion j) E).IsTriangulated

private theorem unit_of_transpose
    {C D : Type*} [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C}
    (a : L ⊣ R) {N : C} {K : D} (c : K ⟶ L.obj N) [IsIso c]
    (x : N ⟶ R.obj K)
    (h : c ≫ (a.homEquiv N K).symm x = 𝟙 K) :
    x ≫ R.map c = a.unit.app N := by
  apply (a.homEquiv N (L.obj N)).symm.injective
  rw [a.homEquiv_naturality_right_symm, a.homEquiv_symm_unit]
  have hx : (a.homEquiv N K).symm x = inv c := by
    apply (cancel_epi c).mp
    simpa only [IsIso.hom_inv_id] using h
  rw [hx, IsIso.inv_hom_id]

private theorem ordinaryOpen_complete {U X : Scheme.{u}}
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    (hU : IsUnit (l : Γ(U, ⊤))) (hX : IsUnit (l : Γ(X, ⊤)))
    (K : DerivedCategory (scalarReductionSource l E U))
    (hK : IsSfDerivedComplete l E U K) :
    IsSfDerivedComplete l E X ((ordinaryOpen l E j).obj K) := by
  obtain ⟨d, hd, hres, hmodels, hopen⟩ := openQuotientKoszulCompleteness l E
  obtain ⟨O, hO⟩ := hopen U X j hU hX
  have hK' := (compactSupport_complete_iff l E U K).mp hK
  have hJ := (compactSupport_complete_iff l E X (O.jShriek.obj K)).mpr (hO K hK').1
  obtain ⟨e⟩ := IntegralSystemRealization.openDvr_ringed_identification l E j O
  exact complete_iso l E X (e.app K) hJ

private def finiteIdentityImage (A : Type u) [CommRing A] [Finite A] (X : Scheme.{u}) :
    proEtaleConstantDerivedDirectImage (𝟙 X) A ≅ 𝟭 (proEtaleDerivedCategory X A) := by
  let e := sfIntrinsicModuleEquivalence X A
  let F := proEtaleConstantModuleDirectImage (𝟙 X) A
  let h : F ≅ 𝟭 _ :=
    (Functor.leftUnitor F).symm ≪≫
      isoWhiskerRight e.counitIso.symm F ≪≫ Functor.associator _ _ _ ≪≫
      isoWhiskerLeft e.inverse (sfIntrinsicDirectImageComparison (𝟙 X) A) ≪≫
      isoWhiskerLeft e.inverse
        (isoWhiskerRight (AlgebraicGeometry.ProEtale.lowerStarId
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) X) e.functor ≪≫
          Functor.leftUnitor e.functor) ≪≫ e.counitIso
  exact Functor.rightDerivedFunctorNatIso h ≪≫
    Functor.rightDerivedFunctorIsoMapDerivedCategory (𝟭 _) ≪≫
    Functor.mapDerivedCategoryIdIso _

private def finiteOpenImage {U X : Scheme.{u}}
    (A : Type u) [CommRing A] [Finite A] (j : U ⟶ X) [IsOpenImmersion j] :
    sfAmbientCompactSupportCandidate A (Compactification.ofIsOpenImmersion j) ≅
      (sfIntrinsicExtensionByZero j A).mapDerivedCategory :=
  isoWhiskerLeft _ (finiteIdentityImage A X) ≪≫ Functor.rightUnitor _

private def openReductionComparison (D : FiniteFieldDatum.{u})
    (primeUnit : IsUnit (l : D.k)) {U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] (n : ℕ) :
    (sfIntegralConstructible l E U).ι ⋙ ordinaryOpen l E j ⋙
        scalarReductionDerivedExtension l E X n ≅
      (sfIntegralConstructible l E U).ι ⋙ scalarReductionDerivedExtension l E U n ⋙
        sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n+1))
          (Compactification.ofIsOpenImmersion j) := by
  let c := Compactification.ofIsOpenImmersion j
  let i := (sfIntegralConstructible l E U).ι
  let q := PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)
  let t := whiskerLeft i (PurCompactSupport.comparison q c)
  let : ∀ K, IsIso (t.app K) :=
    fun K ↦ (sfQcqsCompactSupport_finiteComparison l E D.k primeUnit c K).2 n
  let : IsIso t := NatIso.isIso_of_isIso_app t
  exact isoWhiskerRight (isoWhiskerLeft i (openIdentity l E j).symm)
      (scalarReductionDerivedExtension l E X n) ≪≫
    isoWhiskerLeft (i ⋙ PurCompactSupport.image (PurCompactSupport.completed l E) c)
      (PurCompactSupport.finiteReductionIso l E X n).symm ≪≫
    asIso t ≪≫
    isoWhiskerLeft (i ⋙ pbcDerivedExtend (q.map U))
      (PurCompactSupport.finiteImageIso l E n c) ≪≫
    isoWhiskerRight (isoWhiskerLeft i (PurCompactSupport.finiteReductionIso l E U n))
      (sfAmbientCompactSupportCandidate (Padic.coefficientExtensionRing l E (n+1)) c)

private theorem ordinaryOpen_interval (D : FiniteFieldDatum.{u})
    (primeUnit : IsUnit (l : D.k)) {U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))]
    (K : sfIntegralConstructibleCategory l E U) (a b : ℤ)
    (hK : IntegralImmersionNormalization.HasReductionInterval l E U K.obj a b) :
    IntegralImmersionNormalization.HasReductionInterval l E X
      ((ordinaryOpen l E j).obj K.obj) a b := by
  intro n q hq
  apply hK n
  intro hz
  let A := Padic.coefficientExtensionRing l E (n + 1)
  let : Finite A := Padic.finite_coefficientExtensionRing l E (n + 1)
    (Nat.le_add_left 1 n)
  let F := sfIntrinsicExtensionByZero j A
  let := (sfIntrinsicExtensionByZero_exact j A).1
  let := (sfIntrinsicExtensionByZero_exact j A).2.1
  let := (sfIntrinsicExtensionByZero_exact j A).2.2
  let e := (openReductionComparison l E D primeUnit j n).app K ≪≫
    (finiteOpenImage A j).app ((scalarReductionDerivedExtension l E U n).obj K.obj)
  have hz' := F.map_isZero hz
  have hhom := (F.mapDerivedCategoryHomologyFunctorIso q).app
    ((scalarReductionDerivedExtension l E U n).obj K.obj)
  exact hq (hz'.of_iso
    (((DerivedCategory.homologyFunctor _ q).mapIso e) ≪≫ hhom.symm))

private theorem openSystemReduction_isIso (D : FiniteFieldDatum.{u})
    (primeUnit : IsUnit (l : D.k)) {U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] (K : sfIntegralConstructibleCategory l E U) :
    IsIso ((FrobeniusExchange.compactOperationReduction l E D.k primeUnit j
      (Compactification.ofIsOpenImmersion j)).app K ≫
      (systemDirectId l E X).hom.app
        ((FrobeniusExchange.systemDerivedOpen l E j).obj
          ((FrobeniusExchange.reduction l E U).obj K.obj))) := by
  let c := Compactification.ofIsOpenImmersion j
  let H := FrobeniusExchange.systemDerivedOpen l E j ⋙
    FrobeniusExchange.systemDirect l E (𝟙 X)
  have hi : IsIso ((FrobeniusExchange.operationReduction l E H).app K.obj) := by
    apply (((FrobeniusExchange.models l E).system X).isIso_iff_evaluations _).2
    intro n
    have h := (FrobeniusExchange.compactRealization_existsUnique
      l E D.k primeUnit j c).exists.choose_spec K n
    have hred : IsIso
        ((scalarReductionDerivedExtension l E X n).map
            ((FrobeniusExchange.compactRealization l E D.k primeUnit j c).hom.app K) ≫
          (((FrobeniusExchange.models l E).system X).reductionEvaluation n).inv.app
            ((FrobeniusExchange.compactImage l E j c).obj K.obj) ≫
          (coefficientSequenceDerivedEvaluation l E X n).map
            ((FrobeniusExchange.operationReduction l E H).app K.obj) ≫
          (FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj) :=
      h.symm ▸ (inferInstance :
        IsIso (sfCompactSupportFiniteReductionIso l D.k primeUnit c E K n).hom)
    have hred' : IsIso
        ((((FrobeniusExchange.models l E).system X).reductionEvaluation n).inv.app
            ((FrobeniusExchange.compactImage l E j c).obj K.obj) ≫
          (coefficientSequenceDerivedEvaluation l E X n).map
            ((FrobeniusExchange.operationReduction l E H).app K.obj) ≫
          (FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj) :=
      IsIso.of_isIso_comp_left
        ((scalarReductionDerivedExtension l E X n).map
          ((FrobeniusExchange.compactRealization l E D.k primeUnit j c).hom.app K)) _
    have hred'' : IsIso
        ((coefficientSequenceDerivedEvaluation l E X n).map
            ((FrobeniusExchange.operationReduction l E H).app K.obj) ≫
          (FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj) :=
      IsIso.of_isIso_comp_left
        ((((FrobeniusExchange.models l E).system X).reductionEvaluation n).inv.app
          ((FrobeniusExchange.compactImage l E j c).obj K.obj)) _
    exact IsIso.of_isIso_comp_right _
      ((FrobeniusExchange.compactFiniteEvaluation l E c n).hom.app K.obj)
  change IsIso (((FrobeniusExchange.reduction l E X).map
    ((FrobeniusExchange.compactRealization l E D.k primeUnit j c).hom.app K) ≫
    (FrobeniusExchange.operationReduction l E H).app K.obj) ≫ _)
  infer_instance

/-- Open support comparison and strict-system adjunction maps.
Source: latest blueprint, prop-sf-open-closed-triangle-all-stages.proof.md,
integral and rational support paragraphs; Stacks 03DI, 03DJ, 0941, 099N, 0GL1, 0A07
(blueprint: lem-sf-open-support-normalization).

Proof:
1. Form dj from the canonical compact-support realization and openIdentity.
   Build the finite comparison from the actual coefficient-change isomorphisms;
   cancellation and the realization specification give its projection formula.
2. Open quotient-Koszul completeness applies to all ambient complete objects.
   Transport it through the ringed open identification and completeness equivalence.
3. At each finite level remove identity direct image. Exact extension by zero
   and its homology comparison preserve the same interval, including an empty one.
4. Restrict the ordinary adjunction with the pullback comparison from the open
   Hom-transpose normalization. Its Hom square at the counit gives the system
   counit equation. At an identity it gives the unit equation after cancellation
   of the invertible compact comparison. System evaluations detect only that
   invertibility; equality of morphisms is established before evaluation.
5. Transport CommShift along dj through the fully faithful constructible inclusion.
   Its compatibility lemma gives the specified shift normalization. Transport
   triangulatedness of the ordinary exact-derived extension for this same shift. -/
theorem openSupportNormalization (D : FiniteFieldDatum.{u}) (primeUnit : IsUnit (l : D.k))
    {U X : Scheme.{u}}
    [X.Over (Spec (.of D.k))] [U.Over (Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (U ↘ Spec (.of D.k))] [QuasiCompact (U ↘ Spec (.of D.k))]
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ x : U, Invertible (l : U.residueField x)]
    (j : U ⟶ X) [IsOpenImmersion j] [QuasiCompact j]
    [j.IsOver (Spec (.of D.k))] :
    Nonempty (OpenSupport l E D primeUnit j) := by
  have hunit (T : Scheme.{u}) [T.Over (Spec (.of D.k))] :
      IsUnit (l : Γ(T, ⊤)) := by
    let ρ := (Scheme.ΓSpecIso (.of D.k)).inv ≫ (T ↘ Spec (.of D.k)).appTop
    simpa only [map_natCast] using primeUnit.map ρ.hom
  let d := (sfQcqsCompactSupportRealization l E D.k primeUnit
    (Compactification.ofIsOpenImmersion j)).symm ≪≫
      isoWhiskerLeft (sfIntegralConstructible l E U).ι (openIdentity l E j)
  let := Functor.CommShift.ofComp d ℤ
  obtain ⟨p, hp⟩ := openAdjunctionTransposeNormalization l E D primeUnit j
  let a := (ordinaryOpenAdjunction l E j).restrictFullyFaithful
    (sfIntegralConstructible l E U).fullyFaithfulι
    (sfIntegralConstructible l E X).fullyFaithfulι d.symm p.symm
  have hd : NatTrans.CommShift d.hom ℤ := Functor.CommShift.ofComp_compatibility d ℤ
  have he : (sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
      (Compactification.ofIsOpenImmersion j) E).IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right d).mpr inferInstance
  refine ⟨{
    dj := d
    dj_formula := rfl
    openPull := p
    openComplete := ordinaryOpen_complete l E j (hunit U) (hunit X)
    openInterval := ordinaryOpen_interval l E D primeUnit j
    openReduction := openReductionComparison l E D primeUnit j
    openProjection := by
      intro K n
      let R := scalarReductionDerivedExtension l E X n
      let c := Compactification.ofIsOpenImmersion j
      let τ := sfQcqsCompactSupportRealization l E D.k primeUnit c
      let o := openIdentity l E j
      change R.map (τ.inv.app K ≫ o.hom.app K.obj) ≫
        (R.map (o.inv.app K.obj) ≫
          (PurCompactSupport.finiteReductionIso l E X n).inv.app
            ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj K.obj) ≫
          (PurCompactSupport.comparison
            (PurCompactSupport.reduction l E (n + 1) (Nat.le_add_left 1 n)) c).app K.obj ≫
          (PurCompactSupport.finiteImageIso l E n c).hom.app _ ≫
          (sfAmbientCompactSupportCandidate
            (Padic.coefficientExtensionRing l E (n + 1)) c).map
              ((PurCompactSupport.finiteReductionIso l E U n).hom.app K.obj)) = _
      rw [R.map_comp]
      simp only [Category.assoc, ← R.map_comp_assoc, Iso.hom_inv_id_app]
      erw [Category.comp_id]
      have hs :=
        (sfQcqsCompactSupportRealization_spec l E D.k primeUnit c) K n
      erw [← hs]
      erw [← R.map_comp_assoc, Iso.inv_hom_id_app, R.map_id, Category.id_comp]
    openAdjunction := a
    openAdjunction_formula := rfl
    openSystemUnit := by
      intro N
      have ht := hp N
        ((sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
          (Compactification.ofIsOpenImmersion j) E).obj N) (𝟙 _)
      change (FrobeniusExchange.reduction l E X).map
          (𝟙 (((sfCompactSupportFiniteIntegralFunctor l D.k primeUnit
            (Compactification.ofIsOpenImmersion j) E).obj N).obj)) =
        _ ≫ ((FrobeniusExchange.systemDerivedOpenAdjunction l E j).homEquiv _ _).symm
          ((FrobeniusExchange.reduction l E U).map
            ((a.homEquiv _ _) (𝟙 _)).hom ≫ _) at ht
      rw [a.homEquiv_id, CategoryTheory.Functor.map_id] at ht
      let := openSystemReduction_isIso l E D primeUnit j N
      simpa only [Category.assoc] using
        unit_of_transpose (FrobeniusExchange.systemDerivedOpenAdjunction l E j)
          _ _ ht.symm
    openSystemCounit := by
      intro K
      have ht := hp ((constructibleIntegralPullback l E j).obj K) K
        (a.counit.app K)
      change (FrobeniusExchange.reduction l E X).map (a.counit.app K).hom =
        _ ≫ ((FrobeniusExchange.systemDerivedOpenAdjunction l E j).homEquiv _ _).symm
          ((FrobeniusExchange.reduction l E U).map
            ((a.homEquiv _ _) (a.counit.app K)).hom ≫ _) at ht
      have hc : a.homEquiv _ K (a.counit.app K) = 𝟙 _ := by
        simpa only [a.homEquiv_symm_id] using
          (a.homEquiv _ K).apply_symm_apply
            (𝟙 ((constructibleIntegralPullback l E j).obj K))
      erw [hc, ObjectProperty.FullSubcategory.id_hom,
        CategoryTheory.Functor.map_id, Category.id_comp, Adjunction.homEquiv_counit] at ht
      simpa only [Category.assoc, CategoryTheory.Functor.id_obj] using ht
    openShift := inferInstance
    openShiftNormalization := hd
    openExact := he }⟩

end WeilConjectures.IntegralSupportNormalization
