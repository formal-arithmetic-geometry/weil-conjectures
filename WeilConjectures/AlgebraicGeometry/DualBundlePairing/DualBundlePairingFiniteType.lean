/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DualBundlePairing
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Geometric finiteness of a dual bundle presentation

Source: latest blueprint, lem-fd-base-change.proof.md, cartesian square of
separated finite-type schemes (blueprint: lem-fd-dual-bundle-finite-type).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

private theorem property_of_frames
    (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
    {S V : Scheme.{u}} (π : V ⟶ S) (r : ℕ)
    {I : Type u} (U : I → S.Opens) (cover : (⨆ i, U i) = ⊤)
    (L : I → Scheme.{u}) (p : ∀ i, L i ⟶ (U i).toScheme)
    (j : ∀ i, L i ⟶ V) (square : ∀ i, IsPullback (j i) (p i) π (U i).ι)
    (frame : ∀ i, L i ≅ AffineSpace (ULift.{u} (Fin r)) (U i).toScheme)
    (over : ∀ i, (frame i).hom ≫
      (AffineSpace (ULift.{u} (Fin r)) (U i).toScheme ↘ (U i).toScheme) = p i)
    (hP : ∀ i, P (AffineSpace (ULift.{u} (Fin r)) (U i).toScheme ↘ (U i).toScheme)) :
    P π := by
  apply IsZariskiLocalAtTarget.of_openCover (S.openCoverOfIsOpenCover U cover)
  intro i
  change P (pullback.snd π (U i).ι)
  rw [← P.cancel_left_of_respectsIso (square i).isoPullback.hom,
    (square i).isoPullback_hom_snd, ← over i]
  exact (P.cancel_left_of_respectsIso (frame i).hom _).2 (hP i)

/-- Both projections in a dual bundle presentation are separated and of finite type.

Source: latest blueprint, sec-fourier-transform/sk-thm-inversion/
lem-fd-base-change.proof.md, geometric setting of the cartesian square
(blueprint: lem-fd-dual-bundle-finite-type).

Proof: Locally on the target each projection is isomorphic to the projection
of affine r-space, which is affine and finitely presented. Local finite type,
quasi-compactness and separatedness are invariant under isomorphisms and local
on the target. The local dual frames therefore establish all six assertions.
Empty covers and rank zero are included. -/
theorem DualBundlePairing.finiteType_separated
    {S V Vdual : Scheme.{u}} {π : V ⟶ S} {πdual : Vdual ⟶ S}
    {r : ℕ} {b : Γ(pullback π πdual, ⊤)} (bundle : DualBundlePairing π πdual r b) :
    LocallyOfFiniteType π ∧ QuasiCompact π ∧ IsSeparated π ∧
      LocallyOfFiniteType πdual ∧ QuasiCompact πdual ∧ IsSeparated πdual := by
  have hV (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
      (hP : ∀ i, P (AffineSpace (ULift.{u} (Fin r)) (bundle.U i).toScheme ↘
        (bundle.U i).toScheme)) : P π :=
    property_of_frames P π r bundle.U bundle.cover bundle.localV bundle.πV
      bundle.iV bundle.squareV bundle.frameV bundle.frameV_over hP
  have hD (P : MorphismProperty Scheme.{u}) [IsZariskiLocalAtTarget P]
      (hP : ∀ i, P (AffineSpace (ULift.{u} (Fin r)) (bundle.U i).toScheme ↘
        (bundle.U i).toScheme)) : P πdual :=
    property_of_frames P πdual r bundle.U bundle.cover bundle.localDual bundle.πDual
      bundle.iDual bundle.squareDual bundle.frameDual bundle.frameDual_over hP
  exact ⟨hV (@LocallyOfFiniteType) (fun _ ↦ inferInstance),
    hV (@QuasiCompact) (fun _ ↦ inferInstance), hV (@IsSeparated) (fun _ ↦ inferInstance),
    hD (@LocallyOfFiniteType) (fun _ ↦ inferInstance),
    hD (@QuasiCompact) (fun _ ↦ inferInstance), hD (@IsSeparated) (fun _ ↦ inferInstance)⟩

end AlgebraicGeometry
