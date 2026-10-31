/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.P1.P1KummerChernScalarClassTransport

/-! # Kummer class transport under normalized scalar extension

Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: the Kummer classes over B are images
of those over A (blueprint: lem-sp-p1-kummer-chern-kummer-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

/-- The normalized line insertion carries the actual projective-line Kummer boundary.
Source: literature/blueprint/latest/blueprint/sec-smooth-purity/sk-lem-sp-reduction/
sk-lem-sp-reduction-exceptional.proof.md, Charts: the Kummer classes over B are images
of those over A (blueprint: lem-sp-p1-kummer-chern-kummer-transport).

Proof steps:
1. Evaluate `e.line_normalization` on pure Tate-line generators.
2. Use functoriality of the Kummer connecting class and of `Sheaf.H.map`.
-/
theorem p1KummerChernScalar_kummer_transport
    {A B : Type (u + 1)} [CommRing A] [CommRing B]
    {φ : A →+* B} {N : ℕ} {hA : (N : A) = 0} {hB : (N : B) = 0}
    {S : Scheme.{u}} (hP : IsUnit (N : Γ(ProjectiveLine S, ⊤)))
    (e : P1KummerScalarEndpoints φ N hA hB (ProjectiveLine S)) :
    Sheaf.H.map (p1KummerScalarForgetLineMap e) 2
        (ordinaryFiniteP1KummerClass A N hA S hP) =
      ordinaryFiniteP1KummerClass B N hB S hP := by
  have hroot :
      ordinaryFiniteRootMap A N hA (ProjectiveLine S) ≫
          p1KummerScalarForgetLineMap e =
        ordinaryFiniteRootMap B N hB (ProjectiveLine S) := by
    ext W z
    change e.lineInsertion.hom.app W
      (Scheme.finiteEtaleTateOneGenerator A N (ProjectiveLine S) hA W 1 z) =
      Scheme.finiteEtaleTateOneGenerator B N (ProjectiveLine S) hB W 1 z
    simpa only [map_one] using e.line_normalization W 1 z
  unfold ordinaryFiniteP1KummerClass ordinaryFiniteKummerClass
  rw [← Sheaf.H.map_comp_apply, hroot]

end AlgebraicGeometry.Etale
