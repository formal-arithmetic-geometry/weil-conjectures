/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Native.Pull.NativePullWeilKFlat
public import WeilConjectures.WeilSheaf.Native.NativePullSheafTensor
public import WeilConjectures.CategoryTheory.Native.NativeOpenTensorPresentation
public import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorNormalizedRestrictionDescent
import WeilConjectures.WeilSheaf.Native.NativeNormalizedTensorModels
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorCanonicalData
import WeilConjectures.WeilSheaf.Native.Open.NativeOpenTensorFullKFlatLocalization
import WeilConjectures.WeilSheaf.UpperStarLowerStarAdjunction
import Mathlib.CategoryTheory.Localization.Prod

/-!
# Pullback of native derived Weil tensor products

For any morphism `g : Z ⟶ Y` of separated `k₀`-schemes of finite type, the derived pullback
`g^*` of pro-étale Weil complexes commutes with the native derived tensor product:
`g^*(A ⊗ B) ≅ g^* A ⊗ g^* B`, naturally in `A` and `B`
(`AlgebraicGeometry.ProEtaleWeilSheaf.native_pull_derived_tensor`). On native K-flat
representatives the comparison is the localization of the total-complex comparison obtained
from the balanced sheaf comparison `AlgebraicGeometry.ProEtaleWeilSheaf.native_pull_sheaf_tensor`;
pullback preserves native K-flat complexes
(`AlgebraicGeometry.ProEtaleWeilSheaf.nativeIsKFlat_upperStar`).
-/

@[expose] public section

set_option autoImplicit false

universe u a b

open CategoryTheory CategoryTheory.Limits

namespace NativePullDescentProof

/-- Descent of a total-complex comparison for an exact functor along the full K-flat
localizations, retaining the representative square. -/
theorem derived_comparison
    {A B : Type a} [Category.{b} A] [Category.{b} B] [Abelian A] [Abelian B]
    [HasDerivedCategory.{b} A] [HasDerivedCategory.{b} B]
    (R : B ⥤ A) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (TA : CochainComplex A ℤ ⥤ CochainComplex A ℤ ⥤ CochainComplex A ℤ)
    (TB : CochainComplex B ℤ ⥤ CochainComplex B ℤ ⥤ CochainComplex B ℤ)
    (DA : DerivedCategory A × DerivedCategory A ⥤ DerivedCategory A)
    (DB : DerivedCategory B × DerivedCategory B ⥤ DerivedCategory B)
    (flatA : CochainComplex A ℤ → Prop) (flatB : CochainComplex B ℤ → Prop)
    (hR : ∀ T, flatB T → flatA ((R.mapHomologicalComplex (.up ℤ)).obj T))
    (modelA : ∀ P T, flatA P → flatA T →
      (DA.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TA.obj P).obj T)))
    (modelB : ∀ P T, flatB P → flatB T →
      (DB.obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) ≅
        DerivedCategory.Q.obj ((TB.obj P).obj T)))
    (hnA : ∀ P P' T T' (hP : flatA P) (hP' : flatA P')
      (hT : flatA T) (hT' : flatA T') (f : P ⟶ P') (g : T ⟶ T'),
      DA.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelA P' T' hP' hT').hom =
        (modelA P T hP hT).hom ≫ DerivedCategory.Q.map
          (((TA.map f).app T) ≫ (TA.obj P').map g))
    (hnB : ∀ P P' T T' (hP : flatB P) (hP' : flatB P')
      (hT : flatB T) (hT' : flatB T') (f : P ⟶ P') (g : T ⟶ T'),
      DB.map (Prod.mkHom (DerivedCategory.Q.map f) (DerivedCategory.Q.map g)) ≫
          (modelB P' T' hP' hT').hom =
        (modelB P T hP hT).hom ≫ DerivedCategory.Q.map
          (((TB.map f).app T) ≫ (TB.obj P').map g))
    (t : Functor.uncurry.obj TB ⋙ R.mapHomologicalComplex (.up ℤ) ≅
      (R.mapHomologicalComplex (.up ℤ)).prod (R.mapHomologicalComplex (.up ℤ)) ⋙
        Functor.uncurry.obj TA)
    [((ObjectProperty.ι flatB) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso B (.up ℤ)).inverseImage (ObjectProperty.ι flatB))] :
    ∃ rho : DB ⋙ R.mapDerivedCategory ≅
        R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA,
      OpenTensorRestrictionNormalization R TA TB DA DB
        flatA flatB hR modelA modelB (fun P T ↦ t.app (P, T)) rho := by
  let iB := ObjectProperty.ι flatB
  let qB := iB ⋙ DerivedCategory.Q
  let WB := (HomologicalComplex.quasiIso B (.up ℤ)).inverseImage iB
  let Rc := R.mapHomologicalComplex (.up ℤ)
  let rf := R.mapDerivedCategoryFactors
  let mB : qB.prod qB ⋙ DB ≅ iB.prod iB ⋙ Functor.uncurry.obj TB ⋙ DerivedCategory.Q :=
    NatIso.ofComponents (fun PT ↦ modelB _ _ PT.1.property PT.2.property)
      (fun {PT PT'} fg ↦ hnB _ _ _ _ PT.1.property PT'.1.property
        PT.2.property PT'.2.property fg.1.hom fg.2.hom)
  let mA : ((iB ⋙ Rc) ⋙ DerivedCategory.Q).prod ((iB ⋙ Rc) ⋙ DerivedCategory.Q) ⋙ DA ≅
      (iB ⋙ Rc).prod (iB ⋙ Rc) ⋙ Functor.uncurry.obj TA ⋙ DerivedCategory.Q :=
    NatIso.ofComponents
      (fun PT ↦ modelA _ _ (hR _ PT.1.property) (hR _ PT.2.property))
      (fun {PT PT'} fg ↦ hnA _ _ _ _ (hR _ PT.1.property) (hR _ PT'.1.property)
        (hR _ PT.2.property) (hR _ PT'.2.property) (Rc.map fg.1.hom) (Rc.map fg.2.hom))
  let gg : qB.prod qB ⋙ (DB ⋙ R.mapDerivedCategory) ≅
      qB.prod qB ⋙ (R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ DA) :=
    Functor.isoWhiskerRight mB R.mapDerivedCategory ≪≫
      Functor.isoWhiskerLeft (iB.prod iB ⋙ Functor.uncurry.obj TB) rf ≪≫
      Functor.isoWhiskerRight (Functor.isoWhiskerLeft (iB.prod iB) t) DerivedCategory.Q ≪≫
      mA.symm ≪≫
      Functor.isoWhiskerRight
        (NatIso.prod (Functor.isoWhiskerLeft iB rf).symm
          (Functor.isoWhiskerLeft iB rf).symm) DA
  let ff := Localization.fullyFaithfulWhiskeringLeft (qB.prod qB) (WB.prod WB)
    (DerivedCategory A)
  let rho := ff.preimageIso gg
  refine ⟨rho, ?_⟩
  intro P T hP hT
  have h := NatTrans.congr_app (ff.map_preimage gg.hom) (⟨P, hP⟩, ⟨T, hT⟩)
  change rho.hom.app (DerivedCategory.Q.obj P, DerivedCategory.Q.obj T) =
    gg.hom.app (⟨P, hP⟩, ⟨T, hT⟩) at h
  rw [h]
  dsimp only [gg, mB, mA, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app,
    Functor.isoWhiskerLeft_inv, Iso.symm_hom,
    NatIso.prod_hom, NatTrans.prod, Iso.refl_hom, NatTrans.id_app,
    NatIso.ofComponents_hom_app, NatIso.ofComponents_inv_app]
  dsimp only [iB, qB, Rc, rf, Functor.comp_obj, Functor.prod_obj,
    Functor.uncurry_obj_obj, Functor.id_obj, ObjectProperty.ι_obj]
  simp only [Category.assoc]
  rw [← Functor.map_comp_assoc]
  simp

end NativePullDescentProof

namespace AlgebraicGeometry.ProEtaleWeilSheaf

variable (k₀ : Type u) [Field k₀] [Finite k₀] (l : ℕ) [Fact l.Prime]
  [Fact (ringChar k₀ ≠ l)]
  {Z Y : Scheme.{u}} [Z.Over (Spec (CommRingCat.of k₀))]
  [Y.Over (Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Z ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Z ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Z ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (Y ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (Y ↘ Spec (CommRingCat.of k₀))]
  [IsSeparated (Y ↘ Spec (CommRingCat.of k₀))]
  (g : Z ⟶ Y) [g.IsOver (Spec (CommRingCat.of k₀))]

section

attribute [local irreducible] upperStar nativeTensorTotal nativeDerivedTensor NativeIsKFlat
  nativeOpenTensorModel

set_option maxHeartbeats 1000000 in
-- This assembly combines totalization, localization and the fixed-model square.
/-- The derived tensor comparison for an abstract exact functor between native Weil categories
which commutes with the sheaf tensor product and preserves native K-flat complexes. -/
theorem nonempty_derivedTensorComparison_of_sheafTensor
    (R : ProEtaleWeilSheaf k₀ l Y ⥤ ProEtaleWeilSheaf k₀ l Z)
    [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    [PreservesColimitsOfSize.{0, 0} R]
    (r : nativeOpenSheafTensor k₀ l Y ⋙ R ≅ R.prod R ⋙ nativeOpenSheafTensor k₀ l Z)
    (hR : ∀ T, NativeIsKFlat k₀ l Y T →
      NativeIsKFlat k₀ l Z ((R.mapHomologicalComplex (.up ℤ)).obj T)) :
    Nonempty (nativeDerivedTensor k₀ l Y ⋙ R.mapDerivedCategory ≅
      R.mapDerivedCategory.prod R.mapDerivedCategory ⋙ nativeDerivedTensor k₀ l Z) := by
  obtain ⟨_, _, hTZ, -⟩ := native_open_tensor_canonical_data k₀ l Z
  obtain ⟨_, _, hTY, -⟩ := native_open_tensor_canonical_data k₀ l Y
  obtain ⟨t, -⟩ := NativeRestrictionDescentProof.restriction_total_comparison R
    (nativeTensorBifunctor k₀ l Z).flip (nativeTensorBifunctor k₀ l Y).flip r
  have : ((ObjectProperty.ι (NativeIsKFlat k₀ l Y)) ⋙ DerivedCategory.Q).IsLocalization
      ((HomologicalComplex.quasiIso _ (.up ℤ)).inverseImage
        (ObjectProperty.ι (NativeIsKFlat k₀ l Y))) :=
    native_open_tensor_full_kflat_localization k₀ l Y
  rw [← hTZ, ← hTY] at t
  obtain ⟨mu, -⟩ := NativePullDescentProof.derived_comparison R
    (nativeTensorTotal k₀ l Z) (nativeTensorTotal k₀ l Y)
    (nativeDerivedTensor k₀ l Z) (nativeDerivedTensor k₀ l Y)
    (NativeIsKFlat k₀ l Z) (NativeIsKFlat k₀ l Y) hR
    (nativeOpenTensorModel k₀ l Z) (nativeOpenTensorModel k₀ l Y)
    (fun P P' T T' hP hP' hT hT' f g ↦ by
      unfold nativeOpenTensorModel
      exact (native_normalized_tensor_models k₀ l Z).choose_spec.1 P P' T T' hP hP' hT hT' f g)
    (fun P P' T T' hP hP' hT hT' f g ↦ by
      unfold nativeOpenTensorModel
      exact (native_normalized_tensor_models k₀ l Y).choose_spec.1 P P' T T' hP hP' hT hT' f g)
    t
  exact ⟨mu⟩

/-- **Pullback commutes with the native derived tensor product**: for any morphism
`g : Z ⟶ Y` of separated `k₀`-schemes of finite type, `g^*(A ⊗ B) ≅ g^* A ⊗ g^* B`, naturally in
the pro-étale Weil complexes `A` and `B`. -/
theorem nonempty_nativePullDerivedTensorIso :
    Nonempty (nativeDerivedTensor k₀ l Y ⋙ nativeOpenPull k₀ l g ≅
      (nativeOpenPull k₀ l g).prod (nativeOpenPull k₀ l g) ⋙ nativeDerivedTensor k₀ l Z) := by
  have : (upperStar k₀ l g).IsLeftAdjoint :=
    (upperStarLowerStarAdjunction k₀ l g).isLeftAdjoint
  have : PreservesColimitsOfSize.{0, 0} (upperStar k₀ l g) :=
    (upperStarLowerStarAdjunction k₀ l g).leftAdjoint_preservesColimits
  obtain ⟨r, -⟩ := native_pull_sheaf_tensor k₀ l g
  exact nonempty_derivedTensorComparison_of_sheafTensor k₀ l (upperStar k₀ l g) r
    (nativeIsKFlat_upperStar k₀ l g)

end

end AlgebraicGeometry.ProEtaleWeilSheaf
