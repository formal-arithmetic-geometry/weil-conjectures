/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.Paper.PurEtaleScalarMateProjection
public import Sheaf.AlgebraicGeometry.ProperProjectionFormula
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import all Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import all Sheaf.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
import all WeilConjectures.AlgebraicGeometry.EtaleRestrictScalarsAdjunctionIdentities
import Sheaf.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
import Sheaf.SecSmoothPurity.ScalarPullbackTensorCompatibility

/-! # Proper finite coefficient extension

Source: Stacks Project, `literature/stacks-project/more-etale.tex`, Tag 0GL6,
remark-Rf-lower-shriek-change-of-rings, proper case.
(blueprint: lem-asd-proper-finite-coefficient-extension).

The theorem records the canonical unbounded coefficient-change comparison, its
adjunction normalization, and the identification after restriction of scalars
with the coefficient-first proper projection morphism.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Etale
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale


-- Compare the two right-adjoint mates by their counit transposes.
set_option Elab.async false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restricted_mate_eq
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {FR : C ⥤ D} {GR : D ⥤ C} {FA : E ⥤ F} {GA : F ⥤ E}
    (adjR : FR ⊣ GR) (adjA : FA ⊣ GA)
    (SY : C ⥤ E) (SX : D ⥤ F) (UY : E ⥤ C) (UX : F ⥤ D)
    (TY : C ⥤ C) (TX : D ⥤ D)
    (χ : UY ⋙ FR ≅ FA ⋙ UX) (τ : SY ⋙ FA ≅ FR ⋙ SX)
    (σY : SY ⋙ UY ≅ TY) (σX : SX ⋙ UX ≅ TX)
    (c : ∀ M : C, FR.obj (TY.obj M) ⟶ TX.obj (FR.obj M))
    (hc : ∀ M : C, χ.hom.app (SY.obj M) ≫ UX.map (τ.hom.app M) ≫
        σX.hom.app (FR.obj M) = FR.map (σY.hom.app M) ≫ c M)
    (L : D) (p : TY.obj (GR.obj L) ⟶ GR.obj (TX.obj L))
    (hp : (adjR.homEquiv _ _).symm p =
      c (GR.obj L) ≫ TX.map (adjR.counit.app L)) :
    σY.inv.app (GR.obj L) ≫
        UY.map ((mateEquiv adjR adjA (TwoSquare.mk _ _ _ _ τ.hom)).natTrans.app L) ≫
        (mateEquiv adjA adjR (TwoSquare.mk _ _ _ _ χ.hom)).natTrans.app (SX.obj L) ≫
        GR.map (σX.hom.app L) = p := by
  apply (adjR.homEquiv _ _).symm.injective
  rw [hp, Adjunction.homEquiv_counit]
  simp only [Functor.map_comp, Category.assoc]
  have hn := adjR.counit.naturality (σX.hom.app L)
  simp only [Functor.comp_map, Functor.id_map] at hn
  rw [hn]
  simp only [Functor.comp_obj]
  have hmχ : FR.map ((mateEquiv adjA adjR
      (TwoSquare.mk _ _ _ _ χ.hom)).natTrans.app (SX.obj L)) ≫
      adjR.counit.app (UX.obj (SX.obj L)) =
      χ.hom.app (GA.obj (SX.obj L)) ≫ UX.map (adjA.counit.app (SX.obj L)) :=
    mateEquiv_counit adjA adjR (TwoSquare.mk _ _ _ _ χ.hom) (SX.obj L)
  rw [reassoc_of% hmχ]
  have hnχ := χ.hom.naturality
    ((mateEquiv adjR adjA (TwoSquare.mk _ _ _ _ τ.hom)).natTrans.app L)
  simp only [Functor.comp_obj, Functor.comp_map] at hnχ
  rw [reassoc_of% hnχ]
  have hmτ : FA.map ((mateEquiv adjR adjA
      (TwoSquare.mk _ _ _ _ τ.hom)).natTrans.app L) ≫ adjA.counit.app (SX.obj L) =
      τ.hom.app (GR.obj L) ≫ SX.map (adjR.counit.app L) :=
    mateEquiv_counit adjR adjA (TwoSquare.mk _ _ _ _ τ.hom) L
  rw [← UX.map_comp_assoc, hmτ, UX.map_comp]
  have hnσ := σX.hom.naturality (adjR.counit.app L)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hnσ
  simp only [Category.assoc]
  rw [hnσ, reassoc_of% (hc (GR.obj L))]
  simp only [← FR.map_comp_assoc, Iso.inv_hom_id_app]
  erw [FR.map_id, Category.id_comp]

-- A common abelian K-injective replacement compares both coefficient structures.
-- Restriction itself is not assumed to preserve K-injectivity.
set_option Elab.async false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restricted_kInjective_directImage_quasiIso
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    (I : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A)) ℤ)
    [I.IsKInjective]
    (J : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} R)) ℤ)
    [J.IsKInjective]
    (j : ((Sheaf.restrictScalars X.smallEtaleTopology φ).mapHomologicalComplex
      (.up ℤ)).obj I ⟶ J) [QuasiIso j] :
    QuasiIso (((lowerStar (ModuleCat.{u + 1} R) f).mapHomologicalComplex (.up ℤ)).map j) := by
  let U := moduleAbelianForget R X
  let V := moduleAbelianForget R Y
  let F := lowerStar (ModuleCat.{u + 1} R) f
  let H := lowerStar AddCommGrpCat.{u + 1} f
  have : U.PreservesHomology := inferInstance
  have : V.PreservesHomology := inferInstance
  have : F.Additive := inferInstance
  have : H.Additive := inferInstance
  obtain ⟨K, hK, k, _, hk⟩ := Abelian.HasKInjectiveResolutions.exists_isKInjective
    ((U.mapHomologicalComplex (.up ℤ)).obj J)
  let := hK
  let := hk
  have h₁ : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      ((U.mapHomologicalComplex (.up ℤ)).map j ≫ k)) :=
    moduleAbelianForget_kInjective_directImage_quasiIso A f I K _
  have h₂ : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map k) :=
    moduleAbelianForget_kInjective_directImage_quasiIso R f J K k
  have h₃ : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
      ((U.mapHomologicalComplex (.up ℤ)).map j)) := by
    have : QuasiIso ((H.mapHomologicalComplex (.up ℤ)).map
        ((U.mapHomologicalComplex (.up ℤ)).map j) ≫
        (H.mapHomologicalComplex (.up ℤ)).map k) := by
      rw [← Functor.map_comp]
      exact h₁
    exact quasiIso_of_comp_right _ ((H.mapHomologicalComplex (.up ℤ)).map k)
  have : QuasiIso ((V.mapHomologicalComplex (.up ℤ)).map
      ((F.mapHomologicalComplex (.up ℤ)).map j)) := h₃
  exact (HomologicalComplex.quasiIso_map_iff_of_preservesHomology _ V).mp this

-- Localize the underived mate, then transport from exact to left-derived pullback.
set_option Elab.async false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarRestrictionDirectImageMap_isIso
    {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y) :
    IsIso (scalarRestrictionDirectImageMap φ f) := by
  let e := upperStarRestrictScalarsIsoSheaf φ f
  let eD := (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.mapDerivedCategoryNatIso e ≪≫ Functor.mapDerivedCategoryCompIso _ _
  have hm := derived_mate_exact_eq_square
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (upperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f) e
  rw [underived_mate φ f] at hm
  have hd : IsIso ((mateEquiv
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
      (TwoSquare.mk _ _ _ _ eD.hom)).natTrans) := by
    rw [show (mateEquiv
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
        (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
        (TwoSquare.mk _ _ _ _ eD.hom)).natTrans = _ from hm]
    apply derivedSquare_isIso
    intro I hI
    exact unit_isIso_of_resolution_quasiIso _ _ fun J _ j _ ↦
      restricted_kInjective_directImage_quasiIso φ f I J j
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro K
  have ht := isIso_mate_transport
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) f).symm
    (Iso.refl _) (Iso.refl _) (TwoSquare.mk _ _ _ _ eD.hom) K
  have hs :
      ((((TwoSquare.mk _ _ _ _ eD.hom).whiskerTop (𝟙 _)).whiskerBottom (𝟙 _)).whiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) f).hom).whiskerLeft
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).inv =
        TwoSquare.mk _ _ _ _ (scalarRestrictionPullbackIso φ f).hom := by
    ext M
    simp only [TwoSquare.whiskerTop_app, TwoSquare.whiskerBottom_app,
      TwoSquare.whiskerLeft_app, TwoSquare.whiskerRight_app, TwoSquare.mk,
      NatTrans.id_app, CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
      scalarRestrictionPullbackIso, eD, e, Iso.trans_hom, NatTrans.comp_app,
      Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
      Functor.whiskerLeft_app, Functor.whiskerRight_app, Iso.symm_hom,
      Category.assoc]
  simp only [Iso.symm_hom, Iso.symm_inv, Iso.refl_hom] at ht
  rw [hs] at ht
  exact ht.mpr (inferInstanceAs (IsIso ((mateEquiv
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
    (mapDerivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
    (TwoSquare.mk _ _ _ _ eD.hom)).app K)))


set_option Elab.async false in
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical unbounded proper direct-image comparison for a finite coefficient extension.

Source: Stacks Project, Tag 0GL6, with the counit-transpose normalization of Tag 0B56
and the direct-image composition comparison of Tag 0D6E.
(blueprint: lem-asd-proper-finite-coefficient-extension).

Proof: use the canonical scalar extension and pullback comparison, and take their mate
under the two canonical derived inverse-image/direct-image adjunctions.  Exact restriction
of scalars is conservative and the proper projection theorem makes the coefficient-first
projection morphism invertible.  The canonical restricted direct-image comparison and the
canonical scalar/tensor comparisons identify the restricted mate with that projection;
therefore every component of the mate is invertible.  The mate construction is natural in
all objects, and its defining equation is exactly the displayed counit transpose.  No
flatness of the coefficient map or boundedness of the derived object is used.
-/
theorem properFiniteCoefficientExtension
    {R A : Type (u + 1)} [CommRing R] [CommRing A] [Finite R] [Finite A]
    (φ : R →+* A) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] [IsNoetherian X] [IsNoetherian Y] :
    (∀ L : DerivedCategoryModule R X,
      IsIso ((scalarMate φ f).app L)) ∧
    (∀ L : DerivedCategoryModule R X,
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app
          (scalarCoefficient φ Y)).app
            (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        (scalarTensorIso φ Y).inv.app
          (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
          ((scalarMate φ f).app L) ≫
        (scalarRestrictionDirectImageMap φ f).app
          ((scalarExtension φ X).obj L) ≫
        R((f)_*[ModuleCat.{u + 1} R]).map
          ((scalarTensorIso φ X).hom.app L ≫
            ((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app L).app
              (scalarCoefficient φ X)) =
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app
          (scalarCoefficient φ Y)).app
            (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) f).app L).app
          (scalarCoefficient φ Y) ≫
        R((f)_*[ModuleCat.{u + 1} R]).map
          (((derivedTensor (ModuleCat.{u + 1} R) X).obj L).map
              ((scalarCoefficientPullbackIso φ f).hom) ≫
            ((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app L).app
              (scalarCoefficient φ X))) ∧
    (∀ L : DerivedCategoryModule R X,
      (scalarMate φ f).app L =
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv
          ((scalarExtension φ Y).obj
            (R((f)_*[ModuleCat.{u + 1} R]).obj L))
          ((scalarExtension φ X).obj L)
          ((scalarPullbackIso φ f).hom.app
              (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
            (scalarExtension φ X).map
              ((derivedUpperStarLowerStarAdjunction
                (ModuleCat.{u + 1} R) f).counit.app L))) := by
  have hcomp (L : DerivedCategoryModule R X) :
      (scalarTensorIso φ Y).inv.app (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
          (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
            ((scalarMate φ f).app L) ≫
          (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ X).obj L) ≫
          R((f)_*[ModuleCat.{u + 1} R]).map ((scalarTensorIso φ X).hom.app L) =
        ((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} R) f).app L).app
            (scalarCoefficient φ Y) ≫
          R((f)_*[ModuleCat.{u + 1} R]).map
            (((derivedTensor (ModuleCat.{u + 1} R) X).obj L).map
              (scalarCoefficientPullbackIso φ f).hom) := by
    apply restricted_mate_eq
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
      (scalarExtension φ Y) (scalarExtension φ X)
      (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
      ((derivedTensor (ModuleCat.{u + 1} R) Y).flip.obj (scalarCoefficient φ Y))
      ((derivedTensor (ModuleCat.{u + 1} R) X).flip.obj (scalarCoefficient φ X))
      (scalarRestrictionPullbackIso φ f) (scalarPullbackIso φ f)
      (scalarTensorIso φ Y) (scalarTensorIso φ X)
      (fun C ↦ ((leftDerivedUpperStarTensorComparison (ModuleCat.{u + 1} R) f).app C).app
          (scalarCoefficient φ Y) ≫
        ((derivedTensor (ModuleCat.{u + 1} R) X).obj
          (L((f)^*[ModuleCat.{u + 1} R]).obj C)).map
          (scalarCoefficientPullbackIso φ f).hom)
      (scalarPullback_tensor_compatibility φ f) L
    rw [Adjunction.homEquiv_naturality_right_symm]
    erw [homEquiv_symm_rightDerivedLowerStarProjectionMap]
    simp only [Category.assoc]
    congr 1
    exact (((derivedTensor (ModuleCat.{u + 1} R) X).map
      ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f).counit.app L)).naturality
      (scalarCoefficientPullbackIso φ f).hom).symm
  refine ⟨?_, ?_, ?_⟩
  · intro L
    have := scalarRestrictionDirectImageMap_isIso φ f
    have := isIso_rightDerivedLowerStarProjectionMap_of_finite R f
    have ht : IsIso ((scalarTensorIso φ Y).inv.app
        (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫
        (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map ((scalarMate φ f).app L) ≫
        (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ X).obj L) ≫
        R((f)_*[ModuleCat.{u + 1} R]).map ((scalarTensorIso φ X).hom.app L)) := by
      rw [hcomp]
      infer_instance
    have h₁ := (isIso_comp_left_iff
      ((scalarTensorIso φ Y).inv.app (R((f)_*[ModuleCat.{u + 1} R]).obj L))
      ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map ((scalarMate φ f).app L) ≫
        (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ X).obj L) ≫
        R((f)_*[ModuleCat.{u + 1} R]).map ((scalarTensorIso φ X).hom.app L))).mp ht
    have h₂ : IsIso
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map ((scalarMate φ f).app L) ≫
          (scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ X).obj L)) :=
      (isIso_comp_right_iff _
        (R((f)_*[ModuleCat.{u + 1} R]).map ((scalarTensorIso φ X).hom.app L))).mp
          (by simpa only [Category.assoc] using h₁)
    have : IsIso ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map
        ((scalarMate φ f).app L)) :=
      (isIso_comp_right_iff _
        ((scalarRestrictionDirectImageMap φ f).app ((scalarExtension φ X).obj L))).mp h₂
    have : (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).ReflectsIsomorphisms :=
      exactFunctor_reflects_derived (Sheaf.restrictScalars Y.smallEtaleTopology φ)
    exact isIso_of_reflects_iso _ (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)
  · intro L
    have h := congrArg (fun a ↦
      ((derivedTensorSymmetry (ModuleCat.{u + 1} R) Y).hom.app
          (scalarCoefficient φ Y)).app (R((f)_*[ModuleCat.{u + 1} R]).obj L) ≫ a ≫
        R((f)_*[ModuleCat.{u + 1} R]).map
          (((derivedTensorSymmetry (ModuleCat.{u + 1} R) X).hom.app L).app
            (scalarCoefficient φ X))) (hcomp L)
    simpa only [Functor.map_comp, Category.assoc] using h
  · intro L
    apply (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv
        _ _ |>.symm.injective
    simp only [Functor.comp_obj, Equiv.symm_apply_apply, Adjunction.homEquiv_counit]
    simpa only [scalarMate, TwoSquare.mk] using
      mateEquiv_counit
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} R) f)
        (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f)
        (TwoSquare.mk _ _ _ _ (scalarPullbackIso φ f).hom) L

end AlgebraicGeometry.Etale
