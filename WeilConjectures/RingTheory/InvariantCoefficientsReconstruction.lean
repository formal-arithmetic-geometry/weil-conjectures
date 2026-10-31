/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Reconstruction from invariant coefficients and a common retraction

Source: Stacks Project, `groupoids.tex`, Tag 03C8, `lemma-basis`, right vertical
isomorphism and tensor conclusion, abstracted with invariant coefficients as a hypothesis
(blueprint: lem-a1-invariant-coefficients-reconstruction).
-/

@[expose] public section

universe u v

open scoped BigOperators TensorProduct

namespace RingHom

/-- A unique expansion in the target, with invariant coefficients for the second map,
descends to a basis over the equalizer and identifies the target with the tensor square.
The scalar action on the tensor square is on its first factor.

Source: Stacks Project, `groupoids.tex`, Tag 03C8, `lemma-basis`, final diagram and
right vertical isomorphism, abstracted using the given invariant-coefficient hypothesis
and common retraction (blueprint: lem-a1-invariant-coefficients-reconstruction).

Proof:
1. Expand `τ a` with coefficients in `σ.eqLocus τ`. Applying `ε` gives a spanning
   expansion of `a` in the `x j`. A zero relation over the equalizer becomes, after
   applying `τ` and replacing `τ` by `σ` on its coefficients, a zero relation in `B`.
   Uniqueness of the given expansions forces every coefficient to vanish. Thus `x`
   is a basis, by `def-weil-pbc-free-module`.
2. Apply `lem-weil-pbc-free-module-base-change-free` (`Module.Basis.baseChange`)
   to this basis and the subring inclusion to obtain the first-factor `A`-basis
   `1 ⊗ x j` of the tensor square. This also applies to the zero ring.
3. The restrictions of `σ` and `τ` to their equalizer coincide. The tensor pushout
   property `lem-weil-pbc-algebra-tensor-pushout-universal-property` therefore gives
   the ring map sending `a ⊗ a₂` to `σ a * τ a₂`. Its values on `1 ⊗ x j` are `τ (x j)`;
   its values on `a ⊗ 1` show that it is `A`-linear for the indicated actions.
4. Every given expansion in `B` is the image of the same linear combination of the
   tensor basis, proving surjectivity. Expand a kernel element in that basis:
   uniqueness of the zero expansion in `B` makes all its coordinates zero, proving
   injectivity. The inverse of this bijective ring map preserves the ring operations,
   giving the stated ring equivalence and basis images. -/
theorem invariantCoefficients_reconstruction
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    (σ τ : A →+* B) (ε : B →+* A)
    (hεσ : ε.comp σ = RingHom.id A) (hετ : ε.comp τ = RingHom.id A)
    (r : ℕ) (hr : 1 ≤ r) (x : Fin r → A)
    (hexp : ∀ b : B, ∃! c : Fin r → A, ∑ j, σ (c j) * τ (x j) = b)
    (hinv : ∀ (a : A) (c : Fin r → A),
      (∑ j, σ (c j) * τ (x j)) = τ a → ∀ j, c j ∈ σ.eqLocus τ) :
    ∃ b : Module.Basis (Fin r) (σ.eqLocus τ) A,
      (∀ j, b j = x j) ∧
      ∃ φ : (A ⊗[σ.eqLocus τ] A) ≃+* B,
        (∀ a a₂ : A, φ (a ⊗ₜ[σ.eqLocus τ] a₂) = σ a * τ a₂) ∧
        ∃ e : Module.Basis (Fin r) A (A ⊗[σ.eqLocus τ] A),
          (∀ j, e j = (1 : A) ⊗ₜ[σ.eqLocus τ] x j) ∧
          ∀ j, φ ((1 : A) ⊗ₜ[σ.eqLocus τ] x j) = τ (x j) := by
  sorry

end RingHom
