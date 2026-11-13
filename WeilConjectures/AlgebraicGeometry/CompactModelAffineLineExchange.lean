/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.BaseChangeCharts
import WeilConjectures.SixFunctors.ProjectiveLineExceptionalBaseChange

/-! The affine-line case of exceptional exchange used by the compact-dual model. -/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

/-- The affine-line exchange over any base (no affine hypothesis on `S`). -/
private theorem compactModelAffineLineExchange_aux
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {S : Scheme.{u}} [HasInvertibleExponent Λ S]
    {S' P' : Scheme.{u}} {g : S' ⟶ S} {p' : P' ⟶ S'} {g' : P' ⟶ 𝔸(ULift.{u} (Fin 1); S)}
    (sq : IsPullback g' p' (𝔸(ULift.{u} (Fin 1); S) ↘ S) g) [HasCompactification p']
    [QuasiCompact p'] : IsIso (rightDerivedUpperShriekBaseChangeMap Λ sq) := by
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

/-- The canonical exceptional exchange for an affine-line projection over an affine base,
with finite field coefficients.
Source: blueprint prop-asd-smooth-base-change, affine-line model case, and
lem-asd-smooth-generic-direct-image.proof.md, relative dual base-change step. -/
theorem compactModelAffineLineExchange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (_hfield : IsField Λ) :
    AffineLineBaseChange Λ := by
  intro S
  intros
  exact compactModelAffineLineExchange_aux Λ _

end AlgebraicGeometry.Etale
