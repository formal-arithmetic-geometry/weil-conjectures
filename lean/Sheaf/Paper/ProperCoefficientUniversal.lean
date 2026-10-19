/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.EtaleEssentiallySmall
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar
import Sheaf.Paper.EtaleScalarMateNormalization
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula

/-! # Proper direct image preserves universal coefficient extension

Source: Stacks Project, Tag 0GL6, proper case, using Tag 0F0G.
(blueprint: lem-r2-proper-coefficient-universal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem scalarExtensionIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] {φ : A →+* B}
    (X : Scheme.{u}) {K : DerivedCategoryModule A X} {M : DerivedCategoryModule B X}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj M}
    (hη : Sheaf.IsDerivedBaseChange η) :
    IsIso (((Adjunction.ofIsRightAdjoint
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)).homEquiv K M).symm η) := by
  let adj := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  have hu : Sheaf.IsDerivedBaseChange (adj.unit.app K) := by
    intro N
    convert (adj.homEquiv K N).bijective using 1
    ext g
    exact (adj.homEquiv_unit _ _ g).symm
  exact hu.isIso hη _ (by
    change (adj.homEquiv K M) ((adj.homEquiv K M).symm η) = η
    exact Equiv.apply_symm_apply _ _)

private theorem scalar_image_bounded
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {K : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    {M : _root_.DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (η : K ⟶ (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj M)
    (hη : Sheaf.IsDerivedBaseChange η.hom) :
    _root_.DerivedCategory.TStructure.t.plus
      ((scalarExtension φ Y).obj (R(lowerStar (ModuleCat.{u + 1} A) f).obj K.obj)) := by
  let UX := Sheaf.restrictScalars X.smallEtaleTopology φ
  let UY := Sheaf.restrictScalars Y.smallEtaleTopology φ
  let RA := lowerStar (ModuleCat.{u + 1} A) f
  let adjX := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let c := (adjX.homEquiv K.obj M.obj).symm η.hom
  have : IsIso c := scalarExtensionIso X hη
  let ex : (scalarExtension φ X).obj K.obj ≅ M.obj := asIso c
  let et : ((derivedTensor (ModuleCat.{u + 1} A) X).obj K.obj).obj
      (scalarCoefficient φ X) ≅ UX.mapDerivedCategory.obj M.obj :=
    (scalarTensorIso φ X).symm.app K.obj ≪≫ UX.mapDerivedCategory.mapIso ex
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A f
  let ep : ((derivedTensor (ModuleCat.{u + 1} A) Y).obj
      (RA.rightDerivedFunctor.obj K.obj)).obj (scalarCoefficient φ Y) ≅
      RA.rightDerivedFunctor.obj
        (((derivedTensor (ModuleCat.{u + 1} A) X).obj K.obj).obj
          ((upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor.obj
            (scalarCoefficient φ Y))) :=
    asIso (((rightDerivedLowerStarProjectionMap (ModuleCat.{u + 1} A) f).app K.obj).app
      (scalarCoefficient φ Y))
  let e : UY.mapDerivedCategory.obj
      ((scalarExtension φ Y).obj (RA.rightDerivedFunctor.obj K.obj)) ≅
      RA.rightDerivedFunctor.obj (UX.mapDerivedCategory.obj M.obj) :=
    (scalarTensorIso φ Y).app _ ≪≫ ep ≪≫ RA.rightDerivedFunctor.mapIso
      (((derivedTensor (ModuleCat.{u + 1} A) X).obj K.obj).mapIso
        (scalarCoefficientPullbackIso φ f) ≪≫ et)
  have hb : _root_.DerivedCategory.TStructure.t.plus
      (RA.rightDerivedFunctor.obj (UX.mapDerivedCategory.obj M.obj)) :=
    (_root_.DerivedCategory.TStructure.t.plus).prop_of_iso
      (RA.rightDerivedFunctorPlusCompatibility.app (UX.mapDerivedCategoryPlus.obj M))
      (RA.rightDerivedFunctorPlus.obj (UX.mapDerivedCategoryPlus.obj M)).property
  obtain ⟨a, ha⟩ := (_root_.DerivedCategory.TStructure.t.plus).prop_of_iso e.symm hb
  refine ⟨a, (_root_.DerivedCategory.isGE_iff _ a).2 fun i hi ↦ ?_⟩
  apply UY.isZero_homologyFunctor_of_isZero_homologyFunctor_mapDerivedCategory_obj
  exact (_root_.DerivedCategory.isGE_iff _ a).1 ha i hi


set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Proper direct image carries the universal scalar arrow to the universal scalar
arrow through the canonical restriction/direct-image comparison.
Source: Stacks Tags 0GL6 and 0F0G
(blueprint: lem-r2-proper-coefficient-universal).
Proof: identify a universal scalar presentation with the actual derived scalar
extension by the scalar adjunction. Inverse image commutes with scalar extension
on K-flat representatives by the ordinary balancing map. Its counit mate is the
B-linear coefficient comparison. After restriction to A, the scalar/tensor
identification carries this mate to the proper projection morphism, followed by
the coefficient pullback identification. The proper projection formula for the
finite ring A makes that morphism invertible, without a Noetherian hypothesis on
the schemes. Exact restriction reflects isomorphisms. The scalar-adjunction unit
identity identifies the universal arrow after this isomorphism with direct image
of the given unit followed by the inverse canonical restriction comparison.
The latter comparison is computed on bounded-below injective resolutions, so it
agrees with the ambient counit mate. Hence this displayed arrow is universal
against every ambient B-complex, including unbounded complexes. -/
theorem properCoefficientUniversal
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    {K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))}
    {M : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))}
    (η : K ⟶ (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryPlus.obj M)
    (hη : Sheaf.IsDerivedBaseChange η.hom) :
    Sheaf.IsDerivedBaseChange
      (((lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlus.map η ≫
        (asIso (rightDerivedLowerStarRestrictScalars φ f)).inv.app M).hom) := by
  let UX := Sheaf.restrictScalars X.smallEtaleTopology φ
  let UY := Sheaf.restrictScalars Y.smallEtaleTopology φ
  let RA := lowerStar (ModuleCat.{u + 1} A) f
  let RB := lowerStar (ModuleCat.{u + 1} B) f
  let adjX := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let adjY := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ)
  let c := (adjX.homEquiv K.obj M.obj).symm η.hom
  have : IsIso c := scalarExtensionIso X hη
  let ex : (scalarExtension φ X).obj K.obj ≅ M.obj := asIso c
  have hSX : _root_.DerivedCategory.TStructure.t.plus ((scalarExtension φ X).obj K.obj) :=
    (_root_.DerivedCategory.TStructure.t.plus).prop_of_iso ex.symm M.property
  have hSY := scalar_image_bounded φ f η hη
  have hδM := (scalarMatePlusNormalization φ f).1 M
  have hδ : IsIso ((scalarRestrictionDirectImageMap φ f).app
      ((scalarExtension φ X).obj K.obj)) := by
    apply (isIso_comp_right_iff _
      (RA.rightDerivedFunctor.map (UX.mapDerivedCategory.map ex.hom))).mp
    have hn := (scalarRestrictionDirectImageMap φ f).naturality ex.hom
    dsimp only [Functor.comp_map] at hn
    change IsIso (_ ≫ R(lowerStar (ModuleCat.{u + 1} A) f).map
      ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map ex.hom))
    rw [← hn]
    infer_instance
  have hp := scalarMate_restrict_eq_projection φ f K
    ⟨⟨_, hSX⟩, rfl⟩ ⟨⟨_, hSY⟩, rfl⟩
  have := isIso_rightDerivedLowerStarProjectionMap_of_finite A f
  have hb : IsIso (UY.mapDerivedCategory.map ((scalarMate φ f).app K.obj)) := by
    apply (isIso_comp_right_iff _
      ((scalarRestrictionDirectImageMap φ f).app
        ((scalarExtension φ X).obj K.obj))).mp
    rw [hp]
    infer_instance
  have hβ : IsIso ((scalarMate φ f).app K.obj) := by
    rw [_root_.DerivedCategory.isIso_iff]
    intro n
    have : IsIso (UY.map ((_root_.DerivedCategory.homologyFunctor _ n).map
        ((scalarMate φ f).app K.obj))) :=
      (NatIso.isIso_map_iff (UY.mapDerivedCategoryHomologyFunctorIso n)
        ((scalarMate φ f).app K.obj)).2
        (by rw [Functor.comp_map]; exact inferInstance)
    exact isIso_of_reflects_iso _ UY
  let eA := RA.rightDerivedFunctorPlusCompatibility.app K
  let eB := RB.rightDerivedFunctorPlusCompatibility.app M
  let e : (scalarExtension φ Y).obj (RA.rightDerivedFunctor.obj K.obj) ≅
      (RB.rightDerivedFunctorPlus.obj M).obj :=
    asIso ((scalarMate φ f).app K.obj) ≪≫ RB.rightDerivedFunctor.mapIso ex ≪≫ eB.symm
  have hu : Sheaf.IsDerivedBaseChange
      (adjY.unit.app (RA.rightDerivedFunctor.obj K.obj)) := by
    intro N
    convert (adjY.homEquiv (RA.rightDerivedFunctor.obj K.obj) N).bijective using 1
    ext g
    exact (adjY.homEquiv_unit _ _ g).symm
  have h := (hu.comp_map_iso e).of_iso eA
  have hn := (scalarMatePlusNormalization φ f).2 K M η
  have heq : eA.hom ≫
      (adjY.unit.app (RA.rightDerivedFunctor.obj K.obj) ≫ UY.mapDerivedCategory.map e.hom) =
      (((RA.rightDerivedFunctorPlus.map η) ≫
        (asIso (rightDerivedLowerStarRestrictScalars φ f)).inv.app M).hom) := by
    have hn' := congrArg (fun q ↦ eA.hom ≫ q ≫ UY.mapDerivedCategory.map eB.inv) hn
    dsimp only [e, ex, c, adjX, adjY, eA, eB, RA, RB, UY, Iso.trans_hom,
      Iso.symm_hom, asIso_hom, Functor.mapIso_hom] at hn' ⊢
    simp only [Category.assoc, Iso.app_hom, Iso.app_inv] at hn' ⊢
    simp only [Category.assoc,
      Iso.hom_inv_id_app_assoc, ← CategoryTheory.Functor.map_comp,
      Iso.hom_inv_id_app] at hn'
    exact hn'.trans ((congrArg
      (fun q ↦ (((RA.rightDerivedFunctorPlus.map η) ≫
        (asIso (rightDerivedLowerStarRestrictScalars φ f)).inv.app M).hom) ≫ q)
      ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).map_id
        (RB.rightDerivedFunctorPlus.obj M).obj)).trans (Category.comp_id _))
  rw [heq] at h
  exact h

end AlgebraicGeometry.Etale
