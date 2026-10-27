/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChangeCharts
import Sheaf.SixFunctors.ProjectiveLineExceptionalBaseChange
import WeilConjectures.Compactification.ProjectiveSpace

/-! The affine-line case of exceptional exchange used by the compact-dual model. -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

/-- The canonical exceptional exchange for an affine-line projection over an affine base,
with finite field coefficients.
Source: blueprint prop-asd-smooth-base-change, affine-line model case, and
lem-asd-smooth-generic-direct-image.proof.md, relative dual base-change step.
(blueprint: lem-asd-compact-model-affine-line-exchange).

Proof: Compactify the affine line by the projective line. The projective-line adjunction
identifies its exceptional inverse image with inverse image tensored with the Tate line
and shifted by two. Its counit is the trace pairing, and its unit comes from the supported
diagonal class. Both the trace and the supported diagonal class commute with arbitrary
base change, so the counit equation defining the mate of inverse compact exchange
identifies that mate with the inverse-image and Tate-line comparison, an isomorphism.
For the open affine chart, exceptional restriction equals ordinary restriction; its mate
is the usual inverse-image composition isomorphism. Pasting these two adjunctions proves
invertibility of the canonical affine-line mate. This applies to arbitrary complexes,
including zero, and an empty base gives the unique map in the zero derived category.
The map is the compactification-defined canonical exchange, not a chosen isomorphism. -/
theorem compactModelAffineLineExchange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (_hfield : IsField Λ) :
    AffineLineBaseChange Λ := by
  intro S _ _ S' P' g p' g' sq _ _
  have : QuasiCompact (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S ≫
      ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) := by
    rw [AffineSpace.toRelativeProjectiveSpace_over]
    infer_instance
  have : QuasiCompact (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S) :=
    .of_comp _ (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)
  have : HasCompactification (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S) :=
    (Compactification.ofIsOpenImmersion _).hasCompactification
  exact isIso_rightDerivedUpperShriekBaseChangeMap_of_comp
    (AffineSpace.toRelativeProjectiveSpace (ULift.{u} (Fin 1)) S)
    (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S) (AffineSpace.toRelativeProjectiveSpace_over _ S) sq
    (fun _ _ _ _ _ sq' _ _ ↦
      isIso_rightDerivedUpperShriekBaseChangeMap_of_isOpenImmersion_right Λ sq')
    (fun _ _ _ _ _ sq' _ _ ↦ projectiveLineExceptionalBaseChange Λ S sq')

end AlgebraicGeometry.Etale
