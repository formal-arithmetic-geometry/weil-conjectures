/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q12
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # Fibrewise nonvanishing for a multiplicative function norm

Source: Stacks Project, Divisors, Section 0BCX (section-norms),
Tags 0BCY (lemma-norm-invertible) and 0BCZ (lemma-norm-map-invertible)
(blueprint: lem-sfb-finite-function-norm-nonvanishing).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- A restriction-compatible multiplicative map preserving one and fibrewise vanishing
is nonzero at a base point exactly when the original section is nonzero on its fibre.
The specified complement of the image of the zero locus is an open neighborhood on
which both the original section and its norm have the displayed inverse sections.

Source: Stacks Project, Divisors, Section 0BCX (section-norms),
Tags 0BCY (lemma-norm-invertible) and 0BCZ (lemma-norm-map-invertible)
(blueprint: lem-sfb-finite-function-norm-nonvanishing).

Proof:
1. If the norm is nonzero at `z`, a zero of `b` over `z` contradicts `hν_vanish`.
2. Conversely, assume the fibre lies in `Y.basicOpen b`. This is the open
   nonvanishing locus by `lem-weil-pbc-basic-open-function`. Its complement `C`
   in `p ⁻¹ᵁ V` is relatively closed. Write `C = F ∩ p⁻¹ V` with `F` closed in `Y`.
   By `lem-weil-pbc-finite-closed-map-finite-fibres`, `p` is closed, and
   `p(C) = p(F) ∩ V`. Hence `W = V \ p(C) = V \ p(F)` is open in `Z`.
   The fibre assumption gives `z ∈ W` and `p⁻¹ W ⊆ Y.basicOpen b`.
3. Clause (c) of `lem-weil-pbc-basic-open-function` makes the restriction of `b`
   to its basic open a unit. Restrict its inverse to `p⁻¹ W` to get `c`, with
   `b|p⁻¹ W * c = 1`.
4. Multiplicativity and preservation of one give `ν W (b|p⁻¹ W) * ν W c = 1`.
   Evaluation at `z` in its residue field shows the first factor is nonzero.
   Restriction compatibility identifies it with the value of `ν V b` at `z`.
-/
theorem finite_function_norm_nonvanishing
    {Y Z : Scheme.{u}} (p : Y ⟶ Z) [IsFinite p]
    (ν : ∀ V : Z.Opens, Γ(Y, p ⁻¹ᵁ V) →* Γ(Z, V))
    (hν_restrict : ∀ (V W : Z.Opens) (h : W ≤ V) (b : Γ(Y, p ⁻¹ᵁ V)),
      ν W (Y.presheaf.map (homOfLE (p.preimage_mono h)).op b) =
        Z.presheaf.map (homOfLE h).op (ν V b))
    (hν_vanish : ∀ (V : Z.Opens) (b : Γ(Y, p ⁻¹ᵁ V)) (y : Y) (hy : y ∈ p ⁻¹ᵁ V),
      Y.evaluation (p ⁻¹ᵁ V) y hy b = 0 →
        Z.evaluation V (p y) hy (ν V b) = 0)
    (V : Z.Opens) (b : Γ(Y, p ⁻¹ᵁ V)) (z : Z) (hz : z ∈ V) :
    (Z.evaluation V z hz (ν V b) ≠ 0 ↔ p ⁻¹' {z} ⊆ (Y.basicOpen b : Set Y)) ∧
      (p ⁻¹' {z} ⊆ (Y.basicOpen b : Set Y) →
        ∃ (W : Z.Opens) (hWV : W ≤ V),
          (W : Set Z) = (V : Set Z) \ p '' ((p ⁻¹ᵁ V : Set Y) \ Y.basicOpen b) ∧
          z ∈ W ∧ (p ⁻¹ᵁ W : Set Y) ⊆ Y.basicOpen b ∧
          ∃ c : Γ(Y, p ⁻¹ᵁ W),
            Y.presheaf.map (homOfLE (p.preimage_mono hWV)).op b * c = 1 ∧
            ν W (Y.presheaf.map (homOfLE (p.preimage_mono hWV)).op b) * ν W c = 1) := by
  sorry

end AlgebraicGeometry
