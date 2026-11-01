/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FilteredCondensedRepresentingPair.Pair.FilteredCondensedRepresentingPairData
import all WeilConjectures.SixFunctors.LocallyFiniteAdicRealization.LocallyFiniteAdicCondensedSectionScalarComposition
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.TwoColimit

/-! # A step of filtered condensed representing-pair descent -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
attribute [local irreducible] DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed AlgebraicGeometry.ProEtale.upperStarFromPoint
attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.rightDerivedFunctor CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Mod.extendScalars
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace WeilConjectures.FilteredCondensedRepresentingPair
open CompactSupportCondensedRealization
attribute [local irreducible] HasDerivedCategory.standard
  HasDerivedCategory.ofHasKInjectiveResolutions _root_.instCategoryDerivedCategory
attribute [local instance] fieldSheafAbelian fieldModuleAbelian fieldModuleDerivedCategory

attribute [local instance 2000] AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafMonoidalClosed
  AlgebraicGeometry.ProEtale.hasFunctorialFlatResolution_sheaf
  CategoryTheory.Mod.monoidalCategory CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Mod.hasFunctorialFlatResolution

attribute [local instance] AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj
  fieldGradedFour fieldGradedLeft fieldGradedRight fieldGradedTensor
  fieldTensorColimits fieldTensorColimitsRight fieldModuleFlatResolution

/-- Moving right-adjoint transport across the uniqueness isomorphism. -/
private theorem uniqueness_transport
    {A B : Type*} [Category A] [Category B]
    {F G : A ⥤ B} {R S : B ⥤ A} (a : F ⊣ R) (b : G ⊣ S) (r : R ≅ S) :
    a.leftAdjointUniq (b.ofNatIsoRight r.symm) =
      (a.ofNatIsoRight r).leftAdjointUniq b := by
  apply Iso.ext
  ext M
  apply ((a.ofNatIsoRight r).homEquiv _ _).injective
  rw [Adjunction.homEquiv_leftAdjointUniq_hom_app,
    Adjunction.homEquiv_ofNatIsoRight_apply,
    Adjunction.homEquiv_leftAdjointUniq_hom_app]
  simp [Adjunction.ofNatIsoRight_unit]

section ScalarTensor
variable {Λ Λ' Λ'' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  [MonObj Λ''] [IsCommMonObj Λ'']
  (a : Λ ⟶ Λ') [IsMonHom a] [FlatCoefficientMap a]
  (b : Λ' ⟶ Λ'') [IsMonHom b] [FlatCoefficientMap b]
  [FlatCoefficientMap (a ≫ b)]

/-- The normalized scalar compositor is the recorded exact-derived tensor compositor. -/
private theorem scalar_tensor (W : Scheme.{u}) :
    condensedScalarComp a b W =
      (Functor.leftDerivedFunctorCompIso
        (Mod.extendScalars (coefficientMap a W))
        (Mod.extendScalars (coefficientMap b W))).symm ≪≫
      Functor.leftDerivedFunctorNatIso _
        ((Mod.extendScalarsComp _ _).symm ≪≫
          Mod.extendScalarsIsoOfEq (coefficientMap_comp a b W).symm) := by
  let : BraidedCategory (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1}) :=
    (inferInstance : SymmetricCategory
      (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})).toBraidedCategory
  have hA : IsCommMonObj (condensedRingObj Λ W) :=
    AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ W
  have hB : IsCommMonObj (condensedRingObj Λ' W) :=
    AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ' W
  have hC : IsCommMonObj (condensedRingObj Λ'' W) :=
    AlgebraicGeometry.ProEtale.isCommMonObj_condensedRingObj Λ'' W
  have hφ : PreservesFiniteLimits (Mod.extendScalars (coefficientMap a W)) :=
    (inferInstance : FlatCoefficientMap a) W
  have hψ : PreservesFiniteLimits (Mod.extendScalars (coefficientMap b W)) :=
    (inferInstance : FlatCoefficientMap b) W
  have hχ : PreservesFiniteLimits (Mod.extendScalars (coefficientMap (a ≫ b) W)) :=
    (inferInstance : FlatCoefficientMap (a ≫ b)) W
  have he := @Mod.exactModComp_eq (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC
    (coefficientMap a W) _ (coefficientMap b W) _ (coefficientMap (a ≫ b) W) _ hφ hψ hχ
    (coefficientMap_comp a b W).symm
    (@Mod.homotopyComp_unit (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hB hC
      (coefficientMap a W) _ (coefficientMap b W) _ (coefficientMap (a ≫ b) W) _
      (coefficientMap_comp a b W).symm)
  let α := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap a W)
  let β := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap b W)
  let γ := Mod.derivedExtendMapDerivedCategoryAdjunction (coefficientMap (a ≫ b) W)
  let ρ := Mod.mapDerivedCategoryComapCompIso (coefficientMap a W) (coefficientMap b W)
    (coefficientMap (a ≫ b) W) (coefficientMap_comp a b W).symm
  have hx : condensedScalarComp a b W = Adjunction.leftAdjointCompIso α β γ ρ :=
    (uniqueness_transport (α.comp β) γ ρ).trans
      (leftAdjointCompIso_eq α β γ ρ).symm
  exact hx.trans he.symm

omit [FlatCoefficientMap (a ≫ b)] in
/-- Projection composition with a specified direct coefficient map. -/
private theorem projection_comp_tensor
    (e : Λ ⟶ Λ'') [IsMonHom e] [FlatCoefficientMap e] (he : a ≫ b = e)
    {U V : Scheme.{u}} {g : U ⟶ V} (c : Compactification g)
    (K : DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology U) Ab.{u + 1}) (condensedRingObj Λ U))) :
    (condensedScalar b V).map ((condensedProjection a c).app K) ≫
      (condensedProjection b c).app ((condensedScalar a U).obj K) ≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification Λ'' c).map
        (((Functor.leftDerivedFunctorCompIso
            (Mod.extendScalars (coefficientMap a U))
            (Mod.extendScalars (coefficientMap b U))).symm ≪≫
          Functor.leftDerivedFunctorNatIso _
            ((Mod.extendScalarsComp _ _).symm ≪≫
              Mod.extendScalarsIsoOfEq
                ((coefficientMap_comp a b U).symm.trans
                  (congrArg (fun α ↦ coefficientMap α U) he)))).hom.app K) =
      ((Functor.leftDerivedFunctorCompIso
          (Mod.extendScalars (coefficientMap a V))
          (Mod.extendScalars (coefficientMap b V))).symm ≪≫
        Functor.leftDerivedFunctorNatIso _
          ((Mod.extendScalarsComp _ _).symm ≪≫
            Mod.extendScalarsIsoOfEq
              ((coefficientMap_comp a b V).symm.trans
                (congrArg (fun α ↦ coefficientMap α V) he)))).hom.app
          ((CondensedRing.rightDerivedLowerShriekOfCompactification Λ c).obj K) ≫
        (condensedProjection e c).app K := by
  subst e
  have hc := condensedProjection_comp a b c K
  simp only [scalar_tensor] at hc
  dsimp only [condensedScalar] at hc ⊢
  exact hc

end ScalarTensor

/-- Transport a projection cocycle through the three inclusion comparisons. -/
private theorem transfer_coherence
    {D₀ D₁ D₂ : Type*} [Category D₀] [Category D₁] [Category D₂]
    (T : D₀ ⥤ D₁) (U : D₁ ⥤ D₂) (V : D₀ ⥤ D₂)
    {m₀ n₀ : D₀} {m₁ n₁ : D₁} {m₂ n₂ p₂ q₂ : D₂}
    (i₀ : n₀ ≅ m₀) (i₁ : n₁ ≅ m₁) (j : n₂ ≅ m₂) (j' : q₂ ≅ p₂)
    (a : T.obj m₀ ⟶ m₁) (b : U.obj m₁ ⟶ m₂) (d : V.obj m₀ ⟶ p₂)
    (p : T.obj n₀ ⟶ n₁) (q : U.obj n₁ ⟶ n₂) (r : V.obj n₀ ⟶ q₂)
    (x : m₂ ⟶ p₂) (z : n₂ ⟶ q₂)
    (y : U.obj (T.obj m₀) ⟶ V.obj m₀)
    (y' : U.obj (T.obj n₀) ⟶ V.obj n₀)
    (ha : T.map i₀.inv ≫ p ≫ i₁.hom = a)
    (hb : U.map i₁.inv ≫ q ≫ j.hom = b)
    (hd : V.map i₀.inv ≫ r ≫ j'.hom = d)
    (hc : U.map a ≫ b ≫ x = y ≫ d)
    (hz : z ≫ j'.hom = j.hom ≫ x)
    (hy : U.map (T.map i₀.inv) ≫ y' = y ≫ V.map i₀.inv) :
    U.map p ≫ q ≫ z = y' ≫ r := by
  apply (cancel_mono j'.hom).1
  apply (cancel_epi (U.map (T.map i₀.inv))).1
  calc
    U.map (T.map i₀.inv) ≫ (U.map p ≫ q ≫ z) ≫ j'.hom =
        U.map (T.map i₀.inv ≫ p ≫ i₁.hom) ≫
          (U.map i₁.inv ≫ q ≫ j.hom) ≫ x := by
      simp only [Functor.map_comp, Category.assoc, hz, Iso.map_hom_inv_id_assoc]
    _ = U.map a ≫ b ≫ x := by rw [ha, hb]
    _ = y ≫ d := hc
    _ = U.map (T.map i₀.inv) ≫ (y' ≫ r) ≫ j'.hom := by
      rw [← hd, ← reassoc_of% hy]
      simp only [Category.assoc]

variable (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {f : X ⟶ Y} (c : Compactification f.left)

attribute [local irreducible] constructibleToPadicAlgClCompIso
  CondensedRing.boundedConstructibleLowerShriekOfCompactificationCompatibility
  CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactificationCompatibility

attribute [local irreducible] condensedProjection
  CondensedRing.openImmersionLowerShriek in
set_option linter.unusedSectionVars false in
private theorem field_projection_comp {E H : PadicAlgCl.FiniteIntermediateField l}
    (h : E ≤ H) (M : PadicSubfieldConstructible X.left l E) :
    (derivedExtendScalarsToPadicAlgCl Y.left l H).map
      ((condensedProjection (Profinite.padicSubfieldRingObjMap l h) c).app M.obj) ≫
      (condensedProjection (Profinite.padicSubfieldRingObjToPadicAlgCl l H) c).app
        ((derivedExtendScalarsSubfield X.left l h).obj M.obj) ≫
      (CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.padicAlgClRingObj l) c).map
        ((derivedExtendScalarsCompIso X.left l h).hom.app M.obj) =
    (derivedExtendScalarsCompIso Y.left l h).hom.app
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.continuousMapRingObj E) c).obj M.obj) ≫
      (condensedProjection (Profinite.padicSubfieldRingObjToPadicAlgCl l E) c).app M.obj := by
  simpa only [condensedScalar, derivedExtendScalarsCompIso] using
    (projection_comp_tensor (Profinite.padicSubfieldRingObjMap l h)
      (Profinite.padicSubfieldRingObjToPadicAlgCl l H)
      (Profinite.padicSubfieldRingObjToPadicAlgCl l E)
      (Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl l h) c M.obj)

set_option maxHeartbeats 2000000 in
-- Converting the derived scalar wrappers requires additional definitional reduction.
attribute [local irreducible] condensedProjection
  CondensedRing.openImmersionLowerShriek derivedExtendScalarsCompIso
  finiteCoefficientDerivedTensorCompIso in
/-- Canonical scalar comparisons obey the recorded tensor transitivity cocycle. -/
private theorem scalar_coherence {s : ScalarComparisons l k c}
    (hs : s.IsCanonical l k c) {E H : PadicAlgCl.FiniteIntermediateField l}
    (h : E ≤ H) (M : PadicSubfieldConstructible X.left l E) :
    (constructibleToPadicAlgCl Y.left l H).map ((s.finite h).hom.app M) ≫
      (s.omega H).hom.app ((constructibleExtendScalars X.left l h).obj M) ≫
      (omegaSupport l k c).map
        ((constructibleToPadicAlgClCompIso X.left l h).hom.app M) =
    (constructibleToPadicAlgClCompIso Y.left l h).hom.app
        ((finiteSupport l k c E).obj M) ≫ (s.omega E).hom.app M := by
  have hc := field_projection_comp l k c h M
  have hz := (omegaCompatibility l k c).hom.naturality
    ((constructibleToPadicAlgClCompIso X.left l h).hom.app M)
  dsimp only [Functor.comp_map, ObjectProperty.ι_map] at hz
  erw [tensorComp_hom, ← tensorComp_eq] at hz
  have hy := (derivedExtendScalarsCompIso Y.left l h).hom.naturality
    ((finiteCompatibility l k c E).inv.app M)
  dsimp only [Functor.comp_map] at hy
  apply ObjectProperty.hom_ext
  simp only [ObjectProperty.FullSubcategory.comp_hom, toAlgCl_map_hom,
    tensorComp_hom, ← tensorComp_eq]
  dsimp only [Functor.comp_obj]
  exact transfer_coherence
    (derivedExtendScalarsSubfield Y.left l h)
    (derivedExtendScalarsToPadicAlgCl Y.left l H)
    (derivedExtendScalarsToPadicAlgCl Y.left l E)
    ((finiteCompatibility l k c E).app M)
    ((finiteCompatibility l k c H).app ((constructibleExtendScalars X.left l h).obj M))
    ((omegaCompatibility l k c).app
      ((constructibleToPadicAlgCl X.left l H).obj
        ((constructibleExtendScalars X.left l h).obj M)))
    ((omegaCompatibility l k c).app ((constructibleToPadicAlgCl X.left l E).obj M))
    ((condensedProjection (Profinite.padicSubfieldRingObjMap l h) c).app M.obj)
    ((condensedProjection (Profinite.padicSubfieldRingObjToPadicAlgCl l H) c).app
      ((derivedExtendScalarsSubfield X.left l h).obj M.obj))
    ((condensedProjection (Profinite.padicSubfieldRingObjToPadicAlgCl l E) c).app M.obj)
    (((s.finite h).hom.app M).hom)
    (((s.omega H).hom.app ((constructibleExtendScalars X.left l h).obj M)).hom)
    (((s.omega E).hom.app M).hom)
    ((CondensedRing.rightDerivedLowerShriekOfCompactification
      (Profinite.padicAlgClRingObj l) c).map
        ((derivedExtendScalarsCompIso X.left l h).hom.app M.obj))
    (((omegaSupport l k c).map
      ((constructibleToPadicAlgClCompIso X.left l h).hom.app M)).hom)
    ((derivedExtendScalarsCompIso Y.left l h).hom.app
      ((CondensedRing.rightDerivedLowerShriekOfCompactification
        (Profinite.continuousMapRingObj E) c).obj M.obj))
    ((derivedExtendScalarsCompIso Y.left l h).hom.app
      ((finiteSupport l k c E).obj M).obj)
    (hs.1 h M) (hs.2 H ((constructibleExtendScalars X.left l h).obj M))
    (hs.2 E M) hc hz hy

attribute [local irreducible] constructibleExtendScalars constructibleToPadicAlgCl
  CondensedRing.ContinuousMapRingObj.boundedConstructibleLowerShriekOfCompactification
  CondensedRing.boundedConstructibleLowerShriekOfCompactification

end WeilConjectures.FilteredCondensedRepresentingPair
