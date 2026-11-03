/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Reduction.ReductionDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ProEtale.Open.ProEtaleOpenScalarRestrictionCoherence
public import WeilConjectures.AlgebraicGeometry.OpenScalarTensor.OpenScalarTensorData
import all WeilConjectures.SmoothPurity.Compact.CompactSupportOpenScalarRestriction
import WeilConjectures.CategoryTheory.Exact.ExactLocalizationInverseMate
import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement
import WeilConjectures.CategoryTheory.Normalized.NormalizedAdjunctionComposition

/-! # Scalar restriction preserves the open adjunction unit

Source: Stacks Project, Tags 03DI, 03CY and 015F; the scalar restriction part of
lem-sp-open-scalar-counit-square, Step 2
(blueprint: lem-sp-open-scalar-restriction-unit).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 4096

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale

private theorem exactUnitOnComplexes
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
    (K : CochainComplex C ℤ) :
    a.mapExactDerivedCategory.unit.app (DerivedCategory.Q.obj K) ≫
        G.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
        G.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).unit.app K) := by
  unfold Adjunction.mapExactDerivedCategory
  rw [Adjunction.localization_unit_app]
  simp only [Iso.symm_hom, CatCommSq.iso, Category.assoc]
  rw [← G.mapDerivedCategory.map_comp_assoc, Iso.inv_hom_id_app]
  simp

private theorem exactTranspose
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (a : F ⊣ G)
    (K : CochainComplex C ℤ) (N : CochainComplex D ℤ)
    (f : (F.mapHomologicalComplex (.up ℤ)).obj K ⟶ N) :
    a.mapExactDerivedCategory.homEquiv _ _
        (F.mapDerivedCategoryFactors.hom.app K ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ f) ≫
        G.mapDerivedCategoryFactors.inv.app N := by
  apply (cancel_mono (G.mapDerivedCategoryFactors.hom.app N)).1
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
  simp only [Functor.map_comp, Category.assoc]
  have hn := G.mapDerivedCategoryFactors.hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simpa only [Category.assoc, Functor.comp_obj, Category.comp_id] using congrArg
    (fun k ↦ k ≫ DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f))
    (exactUnitOnComplexes a K)

private theorem exactUniq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F H : C ⥤ D} {G U : D ⥤ C}
    [F.Additive] [H.Additive] [G.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits H] [PreservesFiniteColimits H]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : F ⊣ G) (b : H ⊣ U) (q : G ≅ U) :
    ((a.mapExactDerivedCategory.ofNatIsoRight
        (Functor.mapDerivedCategoryNatIso q)).leftAdjointUniq b.mapExactDerivedCategory) =
      Functor.mapDerivedCategoryNatIso ((a.ofNatIsoRight q).leftAdjointUniq b) := by
  let e := (a.ofNatIsoRight q).leftAdjointUniq b
  let qh : G.mapHomologicalComplex (.up ℤ) ≅ U.mapHomologicalComplex (.up ℤ) :=
    { hom := NatTrans.mapHomologicalComplex q.hom (.up ℤ)
      inv := NatTrans.mapHomologicalComplex q.inv (.up ℤ)
      hom_inv_id := by
        rw [← NatTrans.mapHomologicalComplex_comp, q.hom_inv_id,
          NatTrans.mapHomologicalComplex_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomologicalComplex_comp, q.inv_hom_id,
          NatTrans.mapHomologicalComplex_id] }
  let eh := NatIso.mapHomologicalComplex e (.up ℤ)
  have hv (P : CochainComplex C ℤ) :
      (a.mapHomologicalComplex (.up ℤ)).homEquiv _ _ (eh.hom.app P) ≫
        qh.hom.app ((H.mapHomologicalComplex (.up ℤ)).obj P) =
      (b.mapHomologicalComplex (.up ℤ)).unit.app P := by
    apply HomologicalComplex.Hom.ext
    funext n
    have h := Adjunction.homEquiv_leftAdjointUniq_hom_app (a.ofNatIsoRight q) b (P.X n)
    rw [Adjunction.homEquiv_ofNatIsoRight_apply] at h
    exact h
  have hr (K : CochainComplex D ℤ) :
      G.mapDerivedCategoryFactors.inv.app K ≫
          (Functor.mapDerivedCategoryNatIso q).hom.app (DerivedCategory.Q.obj K) =
        DerivedCategory.Q.map (qh.hom.app K) ≫ U.mapDerivedCategoryFactors.inv.app K := by
    apply (cancel_epi (G.mapDerivedCategoryFactors.hom.app K)).1
    apply (cancel_mono (U.mapDerivedCategoryFactors.hom.app K)).1
    simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Iso.inv_hom_id_app]
    simpa only [qh, Functor.comp_obj, Category.comp_id] using
      Functor.mapDerivedCategoryNatIso_fac q K
  apply Iso.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro P
  apply (cancel_mono (H.mapDerivedCategoryFactors.hom.app P)).1
  rw [Functor.mapDerivedCategoryNatIso_fac]
  exact normalizedAdjunction_uniqueness
    (QA := DerivedCategory.Q) (QB := DerivedCategory.Q)
    (a.mapHomologicalComplex (.up ℤ)) (b.mapHomologicalComplex (.up ℤ))
    a.mapExactDerivedCategory b.mapExactDerivedCategory
    (fun P ↦ F.mapDerivedCategoryFactors.hom.app P)
    (fun P ↦ H.mapDerivedCategoryFactors.hom.app P)
    (fun K ↦ G.mapDerivedCategoryFactors.inv.app K)
    (fun K ↦ U.mapDerivedCategoryFactors.inv.app K)
    (exactTranspose a) (exactTranspose b) qh (Functor.mapDerivedCategoryNatIso q)
    (fun P ↦ eh.hom.app P) hv hr P

private theorem exactRight
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {F : C ⥤ D} {G U : D ⥤ C}
    [F.Additive] [G.Additive] [U.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits U] [PreservesFiniteColimits U]
    (a : F ⊣ G) (q : G ≅ U) :
    a.mapExactDerivedCategory.ofNatIsoRight (Functor.mapDerivedCategoryNatIso q) =
      (a.ofNatIsoRight q).mapExactDerivedCategory := by
  apply Adjunction.ext
  apply Localization.natTrans_ext DerivedCategory.Q (HomologicalComplex.quasiIso C (.up ℤ))
  intro K
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app]
  apply (cancel_mono (U.mapDerivedCategory.map (F.mapDerivedCategoryFactors.hom.app K) ≫
    U.mapDerivedCategoryFactors.hom.app ((F.mapHomologicalComplex (.up ℤ)).obj K))).mp
  have hn := (Functor.mapDerivedCategoryNatIso q).hom.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  simp only [Category.assoc]
  rw [← reassoc_of% hn, Functor.mapDerivedCategoryNatIso_fac]
  rw [exactUnitOnComplexes]
  rw [reassoc_of% (exactUnitOnComplexes a K)]
  rw [← DerivedCategory.Q.map_comp]
  congr 1

private theorem recordedAdjunction (R : Type u) [CommRing R] [Finite R]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (OpenScalarTensor.openAdj R j).ofNatIsoLeft (reductionOpenModel R j).symm =
      ((sfIntrinsicOpenAdjunction R j).ofNatIsoRight
        (openSquarePullbackModel R j).symm).mapExactDerivedCategory := by
  let a := sfIntrinsicOpenAdjunction R j
  let b : proEtaleRingOpenExtension j (proEtaleConstantRing Z R)
      (proEtaleConstantRing X R) (proEtaleConstantRingComparison j R) ⊣
        proEtaleConstantRingPullback R j :=
    Adjunction.ofIsRightAdjoint (proEtaleConstantRingPullback R j)
  let q := (openSquarePullbackModel R j).symm
  have he := exactUniq a b q
  rw [exactRight] at he
  apply Adjunction.ext
  change b.mapExactDerivedCategory.unit ≫ Functor.whiskerRight
    (Functor.mapDerivedCategoryNatIso ((a.ofNatIsoRight q).leftAdjointUniq b)).inv _ = _
  rw [← he]
  ext M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app]
  rw [Adjunction.leftAdjointUniq_inv_app]
  exact Adjunction.unit_leftAdjointUniq_hom_app b.mapExactDerivedCategory
    (a.ofNatIsoRight q).mapExactDerivedCategory M

private theorem pullbackSquare
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) :
    WeilConjectures.compactSupportScalarPullback j φ =
      proEtaleRingRestrictionPullbackInv j
        (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
        (proEtaleConstantRing X A) (proEtaleConstantRing X B)
        (proEtaleConstantRingMap (T := Z) φ) (proEtaleConstantRingMap (T := X) φ)
        (proEtaleConstantRingComparison j A) (proEtaleConstantRingComparison j B)
        (by simpa [proEtaleConstantRingComparison, proEtaleConstantRingMap] using
          (proEtaleConstantInverseImageMap_naturality j
            (a := CommRingCat.ofHom (RingHom.ulift φ))).symm) := by
  let aZ := proEtaleConstantRingMap (T := Z) φ
  let aX := proEtaleConstantRingMap (T := X) φ
  let comm := coefficientInverseImage_naturality j φ
  let d := proEtaleRingRestrictionDirectImage j
    (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
    (proEtaleConstantRing X A) (proEtaleConstantRing X B) aZ aX
    (proEtaleConstantRingComparison j A) (proEtaleConstantRingComparison j B) comm
  have hd : WeilConjectures.compactSupportScalarDirectImage j φ = d := by
    apply (proEtaleRingRestrictionDirectImage_existsUnique j
      (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
      (proEtaleConstantRing X A) (proEtaleConstantRing X B) aZ aX
      (proEtaleConstantRingComparison j A) (proEtaleConstantRingComparison j B) comm).unique
    · exact WeilConjectures.compactSupportScalarDirectImage_sections j φ
    · exact (proEtaleRingRestrictionDirectImage_existsUnique j
        (proEtaleConstantRing Z A) (proEtaleConstantRing Z B)
        (proEtaleConstantRing X A) (proEtaleConstantRing X B) aZ aX
        (proEtaleConstantRingComparison j A) (proEtaleConstantRingComparison j B)
        comm).choose_spec.1
  apply (mateEquiv (proEtaleConstantRingAdjunction B j)
    (proEtaleConstantRingAdjunction A j)).injective
  change (mateEquiv _ _ ((mateEquiv _ _).symm
    (WeilConjectures.compactSupportScalarDirectImage j φ).hom)) = _
  exact (Equiv.apply_symm_apply _ _).trans
    ((congrArg (fun e ↦ TwoSquare.mk _ _ _ _ e.hom) hd).trans
      (congrArg (fun t ↦ TwoSquare.mk _ _ _ _ t)
        (restrictionPullback_mate j _ _ _ _ aZ aX _ _ comm)).symm)

private theorem ordinaryUnit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (M : proEtaleRingModules X (proEtaleConstantRing X B)) :
    ((sfIntrinsicOpenAdjunction A j).ofNatIsoRight
        (openSquarePullbackModel A j).symm).unit.app
        ((proEtaleCoefficientRestrictScalars X φ).obj M) ≫
      (proEtaleConstantRingPullback A j).map ((sfOpenRestriction j φ).hom.app M) ≫
      (WeilConjectures.compactSupportScalarPullback j φ).app
        ((sfIntrinsicExtensionByZero j B).obj M) =
    (proEtaleCoefficientRestrictScalars X φ).map
      (((sfIntrinsicOpenAdjunction B j).ofNatIsoRight
        (openSquarePullbackModel B j).symm).unit.app M) := by
  have hu (R : Type u) [CommRing R] [Finite R]
      (N : proEtaleRingModules X (proEtaleConstantRing X R)) :
      ((sfIntrinsicOpenAdjunction R j).ofNatIsoRight
          (openSquarePullbackModel R j).symm).unit.app N ≫
        (WeilConjectures.compactSupportOpenRestrictionModel R j).hom.app
          ((sfIntrinsicExtensionByZero j R).obj N) =
      (sfIntrinsicExtensionByZeroAdjunction j R).unit.app N := by
    simp only [Adjunction.ofNatIsoRight_unit, Iso.symm_hom, NatTrans.comp_app,
      Functor.whiskerLeft_app, WeilConjectures.compactSupportOpenRestrictionModel,
      Iso.trans_hom, Category.assoc, Iso.inv_hom_id_app_assoc]
    exact WeilConjectures.upperModel_unit R j N
  have h := WeilConjectures.normalizedTransport
    ((sfIntrinsicOpenAdjunction A j).ofNatIsoRight (openSquarePullbackModel A j).symm)
    (sfIntrinsicExtensionByZeroAdjunction j A)
    ((sfIntrinsicOpenAdjunction B j).ofNatIsoRight (openSquarePullbackModel B j).symm)
    (sfIntrinsicExtensionByZeroAdjunction j B)
    (Iso.refl _) (Iso.refl _)
    (WeilConjectures.compactSupportOpenRestrictionModel A j)
    (WeilConjectures.compactSupportOpenRestrictionModel B j)
    (proEtaleCoefficientRestrictScalars X φ) (proEtaleCoefficientRestrictScalars Z φ)
    (WeilConjectures.compactSupportScalarPullback j φ)
    (sfOpenRestrictionCoefficientSquare j φ).hom (sfOpenRestriction j φ).hom
    (by intro N; simpa using hu A N) (by intro N; simpa using hu B N)
    (WeilConjectures.compactSupportOpenRestrictionModel_scalar j φ)
    (sfOpenRestriction_normalized_unique j φ).1 M
  dsimp only [Iso.refl_hom, Iso.refl_inv, NatTrans.id_app] at h
  simp only [Category.id_comp] at h
  rw [(proEtaleCoefficientRestrictScalars Z φ).map_id] at h
  exact h

/-- The specified scalar restriction comparison preserves the unit of the open
adjunction after its prescribed constant-pullback coordinate change.
Source: Stacks Tags 03DI, 03CY and 015F; Step 2 of
lem-sp-open-scalar-counit-square (blueprint: lem-sp-open-scalar-restriction-unit).

Proof: sfOpenRestriction_normalized_unique gives the unit equation before deriving,
with right adjoint sfIntrinsicOpenRestriction and coefficient square
sfOpenRestrictionCoefficientSquare. Identify this restriction with intrinsic pullback
by the open upper-star comparison, and then with proEtaleConstantRingPullback by
openSquarePullbackModel. Both comparisons preserve the sectionwise pullback unit.
The coefficient square in these coordinates is the inverse restriction/pullback square:
on sections the two maps carry the same generator to itself, and respect the same
restricted scalar action. This proves the ordinary unit equation in these coordinates.
Apply it in every degree of an arbitrary cochain complex. The exact-localization unit
formula, mapDerivedCategoryNatIso_fac and the exact composition factors identify its
localization with the claimed equation. Finally reductionOpenModel is the localization
of the left-adjoint uniqueness comparison for this very change of right adjoint, so its
unit equation identifies the transported units with the displayed ones. Equality after
precomposition with the localization functor implies equality of natural transformations,
hence the equation holds at every unbounded derived object. No flatness is used. For
an empty open all source objects are zero; for the whole open this is the identity
restriction square; zero complexes satisfy the same unit equation. -/
theorem openScalarRestrictionUnit
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    ∀ L : proEtaleDerivedCategory X B,
      ((OpenScalarTensor.openAdj A j).ofNatIsoLeft (reductionOpenModel A j).symm).unit.app
          ((scalarRestriction φ X).obj L) ≫
        (constantPullback (A := A) j).map ((sfOpenRestrictionDerived j φ).hom.app L) ≫
        (OpenScalarTensor.rightSquare φ j).inv.app
          ((sfIntrinsicExtensionByZero j B).mapDerivedCategory.obj L) =
      (scalarRestriction φ X).map
        (((OpenScalarTensor.openAdj B j).ofNatIsoLeft (reductionOpenModel B j).symm).unit.app L)
    := by
  let a := (sfIntrinsicOpenAdjunction A j).ofNatIsoRight
    (openSquarePullbackModel A j).symm
  let b := (sfIntrinsicOpenAdjunction B j).ofNatIsoRight
    (openSquarePullbackModel B j).symm
  have hi : IsIso (WeilConjectures.compactSupportScalarPullback j φ) :=
    WeilConjectures.compactSupportScalarPullback_isIso j φ
  let d : proEtaleConstantRingPullback B j ⋙ proEtaleCoefficientRestrictScalars X φ ≅
      proEtaleCoefficientRestrictScalars Z φ ⋙ proEtaleConstantRingPullback A j :=
    (asIso (WeilConjectures.compactSupportScalarPullback j φ)).symm
  let β := sfOpenRestriction j φ
  have hβ (M : proEtaleRingModules X (proEtaleConstantRing X B)) :
      a.unit.app ((proEtaleCoefficientRestrictScalars X φ).obj M) ≫
        (proEtaleConstantRingPullback A j).map (β.hom.app M) =
      (proEtaleCoefficientRestrictScalars X φ).map (b.unit.app M) ≫
        d.hom.app ((sfIntrinsicExtensionByZero j B).obj M) := by
    apply (cancel_mono (d.inv.app ((sfIntrinsicExtensionByZero j B).obj M))).mp
    simp only [Category.assoc, Iso.hom_inv_id_app]
    exact ordinaryUnit φ j M
  have he : ((mateEquiv b a).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans = β.hom := by
    apply NatTrans.ext
    funext M
    apply (a.homEquiv _ _).injective
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit]
    exact (unit_mateEquiv_symm b a (TwoSquare.mk _ _ _ _ d.hom) M).symm.trans (hβ M).symm
  have : IsIso ((mateEquiv b a).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans := by
    rw [he]
    infer_instance
  have hm := (exact_localization_inverse_mate b a d).2.1
  have he' : asIso ((mateEquiv b a).symm (TwoSquare.mk _ _ _ _ d.hom)).natTrans = β :=
    Iso.ext he
  rw [he'] at hm
  have hd : (Functor.mapDerivedCategorySquareIso d).hom =
      (OpenScalarTensor.rightSquare φ j).hom := by
    dsimp only [d, OpenScalarTensor.rightSquare, proEtaleRingRestrictionDerivedPullback,
      Functor.mapDerivedCategorySquareIso]
    congr 3
    congr 1
    apply congrArg Iso.symm
    apply Iso.ext
    exact pullbackSquare φ j
  rw [hd] at hm
  intro L
  have hu := unit_mateEquiv_symm (exactLocalizationDerivedAdjunction b)
    (exactLocalizationDerivedAdjunction a)
    (TwoSquare.mk _ _ _ _ (OpenScalarTensor.rightSquare φ j).hom) L
  change _ = _ ≫ (proEtaleConstantRingPullback A j).mapDerivedCategory.map
    (((mateEquiv _ _).symm _).natTrans.app L) at hu
  have hmL := NatTrans.congr_app hm L
  erw [hmL] at hu
  rw [recordedAdjunction A j, recordedAdjunction B j]
  apply (cancel_mono ((OpenScalarTensor.rightSquare φ j).hom.app
    ((sfIntrinsicExtensionByZero j B).mapDerivedCategory.obj L))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  erw [Category.comp_id]
  change a.mapExactDerivedCategory.unit.app ((scalarRestriction φ X).obj L) ≫
      (constantPullback (A := A) j).map ((sfOpenRestrictionDerived j φ).hom.app L) =
    (scalarRestriction φ X).map (b.mapExactDerivedCategory.unit.app L) ≫
      (OpenScalarTensor.rightSquare φ j).hom.app
        ((sfIntrinsicExtensionByZero j B).mapDerivedCategory.obj L)
  exact hu.symm

end AlgebraicGeometry.ProEtale
