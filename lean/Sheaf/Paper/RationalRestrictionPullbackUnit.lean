/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T4
-/
module

public import Sheaf.Paper.FiniteRationalDerivedOperations
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The scalar-unit equation for rational restriction and pullback

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14(2), Remark 6.8.15;
step 2 of the finite rational coefficient argument.
(blueprint: lem-sf-rational-restriction-pullback-unit).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry
namespace WeilConjectures

/-- Restriction commutes with pullback by an isomorphism satisfying the explicit
unit equation for the normalized scalar comparison.

Source: Bhatt--Scholze, Lemma 6.7.2, Proposition 6.8.14(2), Remark 6.8.15;
step 2 of lem-sf-rational-pullback-scalar-right-mate.
(blueprint: lem-sf-rational-restriction-pullback-unit).

Proof: first take U_X and U_Y to be coefficient restriction, with the adjunction
units given by the trace-dual-basis formula m ↦ sum_i b_i tensor c_i m.
Forgetting the F action commutes with termwise inverse image. It also commutes
with the reductions and limits defining completed pullback: restriction is
exact, preserves limits, and the two uniformizer filtrations are cofinal.
This gives the natural isomorphism e from pullback then restriction to
restriction then pullback on complete constructible complexes. Its inverse
is the same identification in the other direction. Localize the maps to raw
rational constructible categories.

For K represented by a flat-term K-flat complex, both sides of the displayed
equation send a section m to the same sum_i b_i tensor c_i m after pullback.
Use finiteFreeCompletedScalarComparison to replace ordinary coefficient
tensor by normalized completed tensor. The representative normalization of
scalarPullbackCompleted and the component specification of
rationalPullbackScalarComparison identify this tensor map with the inverse
comparison appearing below. Thus the equation holds for exactly that map.
K-flat resolutions, naturality and localization extend the equality to every
K. Common denominators in the two dual bases are inverted, so no perfect
integral trace pairing is required, including for ramified extensions.

For the supplied adjunctions bX and bY, use left-adjoint uniqueness with the
identity transformation on the fixed scalar right adjoints. Conjugate e by
these two uniqueness isomorphisms. Their defining unit equations transport
the displayed identity to bX and bY, proving the assertion for arbitrary
supplied left adjoints. Repeated fields, zero complexes and empty schemes
satisfy the same formulas. No geometric right adjoints occur in this step. -/
theorem rationalRestrictionPullback_unit
    (l : ℕ) [Fact l.Prime]
    (E F : Type u) [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]
    [Field F] [Algebra ℚ_[l] F] [FiniteDimensional ℚ_[l] F]
    (ι : E →ₐ[ℚ_[l]] F) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (l : X.residueField x)]
    [∀ y : Y, Invertible (l : Y.residueField y)]
    (UX : sfRationalConstructibleCategory l F X ⥤ sfRationalConstructibleCategory l E X)
    (UY : sfRationalConstructibleCategory l F Y ⥤ sfRationalConstructibleCategory l E Y)
    (bX : UX ⊣ sfRationalScalarExtension l E X 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι)
    (bY : UY ⊣ sfRationalScalarExtension l E Y 0
      (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι) :
    ∃ e : rationalDerivedPullback l F f ⋙ UX ≅ UY ⋙ rationalDerivedPullback l E f,
      ∀ K : sfRationalConstructibleCategory l F Y,
        (rationalDerivedPullback l F f).map (bY.unit.app K) ≫
          (rationalPullbackScalarComparison l E F ι f).inv.app (UY.obj K) =
        bX.unit.app ((rationalDerivedPullback l F f).obj K) ≫
          (sfRationalScalarExtension l E X 0
            (Nat.Prime.ne_zero (Fact.out : l.Prime)) F ι).map (e.hom.app K) := by
  sorry

end WeilConjectures
