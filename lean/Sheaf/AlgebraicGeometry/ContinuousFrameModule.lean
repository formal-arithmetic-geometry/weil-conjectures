/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.LisseLatticeCoefficientsSized
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Topology.Algebra.Module.Basic
public import Sheaf.CategoryTheory.RingedSiteModules
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import Mathlib.AlgebraicGeometry.Sites.ConstantSheaf
import Mathlib.CategoryTheory.Sites.Sheafification

/-! # Continuous module sections on the small pro-etale site

Source: blueprint, stratified lattice proof, paragraph "Pushing down by the trace".
(blueprint: def-sfb-continuous-frame-module)

The constructions specify the actual continuous-section presheaves and their scalar
extension. Sheafification uses the existing change-of-rings API, with independent site
and coefficient universes.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u v

open CategoryTheory Opposite
open scoped TensorProduct ChangeOfRings

namespace AlgebraicGeometry.ProEtale

/-- Continuous module-valued sections with pointwise action and precomposition restrictions.
Source: blueprint, stratified lattice proof, "Pushing down by the trace".
(blueprint: def-sfb-continuous-frame-module) -/
def continuousFramePresheaf (X : Scheme.{u}) (T M : Type v)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [Module T M] [ContinuousSMul T M] :
    PresheafOfModules.{max (u + 1) v}
      ((lisseContinuousCommRingSheafUniverses X T).obj ⋙
        forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v}) where
  obj U := ModuleCat.of (ULift.{u + 1} C(U.unop.left, T)) (ULift.{u + 1} C(U.unop.left, M))
  map {_U V} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars
      (((lisseContinuousCommRingSheafUniverses X T).obj ⋙
        forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v}).map f).hom).obj
          (ModuleCat.of (ULift.{u + 1} C(V.unop.left, T)) (ULift.{u + 1} C(V.unop.left, M))))
    { toFun := fun g ↦ ULift.up (g.down.comp f.unop.left.base.hom)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Bundle the specified continuous presheaf once its sheaf condition has been supplied.
Source: blueprint, stratified lattice proof, "Pushing down by the trace".
(blueprint: def-sfb-continuous-frame-module) -/
def continuousFrameSheaf (X : Scheme.{u}) (T M : Type v)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [Module T M] [ContinuousSMul T M]
    (h : Presheaf.IsSheaf (Scheme.ProEt.topology X)
      (continuousFramePresheaf X T M).presheaf) :
    ringedSiteModules.{max (u + 1) v}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v})).obj
        (lisseContinuousCommRingSheafUniverses X T)) :=
  ⟨continuousFramePresheaf X T M, h⟩

/-- The actual coefficient inclusion, given by postcomposition with the subring inclusion.
Source: blueprint, stratified lattice proof, "Pushing down by the trace".
(blueprint: def-sfb-continuous-frame-module) -/
def continuousFrameCoefficientInclusion (X : Scheme.{u}) (K : Type v)
    [Field K] [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K) :
    lisseContinuousCommRingSheafUniverses X A ⟶ lisseContinuousCommRingSheafUniverses X K :=
  ⟨{ app := fun _ ↦ CommRingCat.ofHom
       (ULift.ringEquiv.symm.toRingHom.comp
         ((A.subtype.compLeftContinuous _ continuous_subtype_val).comp
           ULift.ringEquiv.toRingHom))
     naturality := fun _ _ _ ↦ rfl }⟩

/-- The pointwise module action on lifted continuous sections over the named coefficient ring.
Source: blueprint, stratified lattice proof, "Pushing down by the trace".
(blueprint: def-sfb-continuous-frame-module) -/
instance continuousFrameSectionsModule (X : Scheme.{u}) (T M : Type v)
    [CommRing T] [TopologicalSpace T] [IsTopologicalRing T]
    [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [Module T M] [ContinuousSMul T M] (U : X.ProEtᵒᵖ) :
    Module ((lisseContinuousCommRingSheafUniverses X T).obj.obj U)
      (ULift.{u + 1} C(U.unop.left, M)) :=
  inferInstanceAs (Module (ULift.{u + 1} C(U.unop.left, T))
    (ULift.{u + 1} C(U.unop.left, M)))

/-- Additive sheafification on the site in the larger coefficient universe.
Source: Mathlib small-site sheafification; blueprint, stratified lattice proof.
(blueprint: def-sfb-continuous-frame-module) -/
instance continuousFrameHasSheafify (X : Scheme.{u}) :
    HasSheafify (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v} :=
  letI : EssentiallySmall.{max (u + 1) v} X.ProEt := essentiallySmallSelf.{v} X.ProEt
  letI : HasSheafify
      ((equivSmallModel.{max (u + 1) v} X.ProEt).inverse.inducedTopology
        (Scheme.ProEt.topology X)) AddCommGrpCat.{max (u + 1) v} :=
    GrothendieckTopology.hasSheafify_of_isGrothendieckAbelian _ _
  hasSheafifyEssentiallySmallSite (Scheme.ProEt.topology X) AddCommGrpCat.{max (u + 1) v}

/-- Local bijectivity detects sheafification equivalences in the coefficient universe.
Source: Mathlib small-site sheafification; blueprint, stratified lattice proof.
(blueprint: def-sfb-continuous-frame-module) -/
instance continuousFrameWEquals (X : Scheme.{u}) :
    (Scheme.ProEt.topology X).WEqualsLocallyBijective AddCommGrpCat.{max (u + 1) v} :=
  letI : EssentiallySmall.{max (u + 1) v} X.ProEt := essentiallySmallSelf.{v} X.ProEt
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall
    (A := AddCommGrpCat.{max (u + 1) v}) (Scheme.ProEt.topology X)

/-- The existing sectionwise change of rings, with the site arguments made explicit.
Source: blueprint, stratified lattice proof, "Pushing down by the trace".
(blueprint: def-sfb-continuous-frame-module) -/
abbrev continuousFrameTensorPresheaf (X : Scheme.{u}) (K : Type v)
    [Field K] [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K)
    (F : ringedSiteModules.{max (u + 1) v}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v})).obj
          (lisseContinuousCommRingSheafUniverses X A))) :=
  letI := continuousFrameHasSheafify.{u, v} X
  letI := continuousFrameWEquals.{u, v} X
  SheafOfModules.changeOfRingsPresheafOfUniverses.{u, u + 1, max (u + 1) v,
    max (u + 1) v} (C := X.ProEt)
    (J := Scheme.ProEt.topology X)
    (R₁ := lisseContinuousCommRingSheafUniverses X A)
    (R₂ := lisseContinuousCommRingSheafUniverses X K)
    (continuousFrameCoefficientInclusion X K A) F

/-- The existing sheaf change of rings of the continuous-section module.
Source: blueprint, stratified lattice proof, "Pushing down by the trace".
(blueprint: def-sfb-continuous-frame-module) -/
abbrev continuousFrameTensorSheaf (X : Scheme.{u}) (K : Type v)
    [Field K] [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K)
    (F : ringedSiteModules.{max (u + 1) v}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v})).obj
          (lisseContinuousCommRingSheafUniverses X A))) :=
  letI := continuousFrameHasSheafify.{u, v} X
  letI := continuousFrameWEquals.{u, v} X
  SheafOfModules.changeOfRingsOfUniverses.{u, u + 1, max (u + 1) v,
    max (u + 1) v} (C := X.ProEt)
    (J := Scheme.ProEt.topology X)
    (R₁ := lisseContinuousCommRingSheafUniverses X A)
    (R₂ := lisseContinuousCommRingSheafUniverses X K)
    (continuousFrameCoefficientInclusion X K A) F

/-- The canonical unit from sectionwise tensors to the sheaf tensor product.
Source: blueprint, stratified lattice proof, "Pushing down by the trace".
(blueprint: def-sfb-continuous-frame-module) -/
def continuousFrameTensorUnit (X : Scheme.{u}) (K : Type v)
    [Field K] [TopologicalSpace K] [IsTopologicalRing K] (A : Subring K)
    (F : ringedSiteModules.{max (u + 1) v}
      ((sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v})).obj
          (lisseContinuousCommRingSheafUniverses X A))) :
    continuousFrameTensorPresheaf X K A F ⟶ (continuousFrameTensorSheaf X K A F).val :=
  letI := continuousFrameHasSheafify.{u, v} X
  letI := continuousFrameWEquals.{u, v} X
  (PresheafOfModules.sheafificationAdjunction.{max (u + 1) v, u, max (u + 1) v, u + 1}
    (R := (sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{max (u + 1) v} RingCat.{max (u + 1) v})).obj
        (lisseContinuousCommRingSheafUniverses X K)) (𝟙 _)).unit.app
          (continuousFrameTensorPresheaf X K A F)



end AlgebraicGeometry.ProEtale
