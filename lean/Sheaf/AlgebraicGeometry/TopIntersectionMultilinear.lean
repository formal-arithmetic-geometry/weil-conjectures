/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Sheaf.AlgebraicGeometry.IntersectionNumber
public import WeilConjectures.AlgebraicGeometry.Picard.Group
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.Multilinear.Basic
import Mathlib.Algebra.Polynomial.Roots
import Sheaf.AlgebraicGeometry.SnapperNumericalPolynomial
import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
import WeilConjectures.AlgebraicGeometry.Modules.Invertible

/-! # Multilinearity of top intersection numbers

Source: Stacks Project, Varieties, Definition 0BEP and Lemma 0BER, and the rational
multilinear extension of its additive pairing (blueprint: lem-sfb-top-intersection-multilinear).

The rational space of line-bundle classes modulo tensor-product relations is the existing
Picard group, written additively and tensored with `ℚ` over `ℤ`. No new Picard group or
intersection-number definition is introduced.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory MonoidalCategory
open scoped TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

/-- Top intersection numbers are invariant under isomorphism, symmetric, tensor-additive
in each slot, zero with a trivial slot, and negated by dualizing a slot. They extend uniquely
to a symmetric rational multilinear pairing on the rationalized Picard group.
Source: Stacks Project, Varieties, Definition 0BEP and Lemma 0BER
(blueprint: lem-sfb-top-intersection-multilinear).

Proof (for stage 3):
1. Apply `lem-sc-snapper-numerical-polynomial` to the identity closed immersion and
   `O_X`, whose support has dimension `g`. Polynomials agreeing on all integer tuples
   agree: induct on the number of variables, applying
   `lem-trf-polynomial-infinite-evaluation-identity` over `ℚ` in one variable at a time.
2. Entry isomorphisms give isomorphic tensor twists, so their cohomology dimensions and
   `def-pc-euler-characteristic` agree. Permutations permute the polynomial's variables,
   fixing the coefficient of their product. This proves invariance and symmetry by
   `def-sc-intersection-number`.
3. Fix the other `g - 1` slots and apply Snapper to them together with `M` and `N`, giving
   `Q(t,u,v)` of total degree at most `g`. The polynomials for their tensor product and
   the two separate entries are `Q(t,z,z)`, `Q(t,z,0)`, and `Q(t,0,z)`, respectively;
   this holds on integer tuples, including negative powers by duality, hence identically.
   Only the monomials with all other exponents one and `(u,v)` exponents `(1,0)` or
   `(0,1)` contribute to the coefficient of the product of the `t` variables times `z`.
   Their coefficients add, proving tensor-additivity in every slot (Tag 0BER).
4. Since `O_X ⊗ O_X` is isomorphic to `O_X`, additivity implies its slot value is zero.
   The evaluation isomorphism `L ⊗ L.dual ≅ O_X` of `def-sc-invertible-module` then
   implies that dualizing a slot negates the value.
5. For finite rational sums in every slot, sum the original intersection values with
   coefficients given by the products of their rational coefficients. Isomorphism
   invariance makes this independent of representatives, and additivity annihilates
   every tensor-product relation in every slot. Hence it descends to the rationalized
   Picard group. Distributivity gives rational multilinearity and step 2 gives symmetry.
   Rationalized line-bundle classes span that space, so multilinearity forces the same
   finite-sum formula for every extension, proving uniqueness. The bound `1 ≤ g` ensures
   the slot assertions concern an actual entry. -/
theorem top_intersection_multilinear
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))] [Nonempty X] (g : ℕ) (_hg : 1 ≤ g)
    (hd : topologicalKrullDim X = ((g : ℕ∞) : WithBot ℕ∞)) :
    (∀ (L M : Fin g → X.Modules) [∀ j, (L j).IsInvertible] [∀ j, (M j).IsInvertible],
      (∀ j, Nonempty (L j ≅ M j)) →
      intersectionNumber k X X (𝟙 X) g hd L = intersectionNumber k X X (𝟙 X) g hd M) ∧
    (∀ (L M : Fin g → X.Modules) [∀ j, (L j).IsInvertible] [∀ j, (M j).IsInvertible]
      (σ : Equiv.Perm (Fin g)), (∀ j, Nonempty (M j ≅ L (σ j))) →
      intersectionNumber k X X (𝟙 X) g hd M = intersectionNumber k X X (𝟙 X) g hd L) ∧
    (∀ (L M N : Fin g → X.Modules) [∀ j, (L j).IsInvertible]
      [∀ j, (M j).IsInvertible] [∀ j, (N j).IsInvertible] (i : Fin g),
      (∀ j, j ≠ i → M j = L j ∧ N j = L j) → Nonempty (L i ≅ M i ⊗ N i) →
      intersectionNumber k X X (𝟙 X) g hd L =
        intersectionNumber k X X (𝟙 X) g hd M + intersectionNumber k X X (𝟙 X) g hd N) ∧
    (∀ (L : Fin g → X.Modules) [∀ j, (L j).IsInvertible] (i : Fin g),
      Nonempty (L i ≅ 𝟙_ X.Modules) → intersectionNumber k X X (𝟙 X) g hd L = 0) ∧
    (∀ (L M : Fin g → X.Modules) [∀ j, (L j).IsInvertible] [∀ j, (M j).IsInvertible]
      (i : Fin g), (∀ j, j ≠ i → M j = L j) → Nonempty (M i ≅ (L i).dual) →
      intersectionNumber k X X (𝟙 X) g hd M = -intersectionNumber k X X (𝟙 X) g hd L) ∧
    (∃ F : MultilinearMap ℚ (fun _ : Fin g ↦ ℚ ⊗[ℤ] Additive X.Pic) ℚ,
      (∀ (σ : Equiv.Perm (Fin g)) (v : Fin g → ℚ ⊗[ℤ] Additive X.Pic),
        F (v ∘ σ) = F v) ∧
      (∀ (L : Fin g → X.Modules) [∀ j, (L j).IsInvertible],
        F (fun j ↦ (1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul (Pic.ofIsInvertible (L j))) =
          intersectionNumber k X X (𝟙 X) g hd L) ∧
      ∀ G : MultilinearMap ℚ (fun _ : Fin g ↦ ℚ ⊗[ℤ] Additive X.Pic) ℚ,
        (∀ (L : Fin g → X.Modules) [∀ j, (L j).IsInvertible],
          G (fun j ↦ (1 : ℚ) ⊗ₜ[ℤ] Additive.ofMul (Pic.ofIsInvertible (L j))) =
            intersectionNumber k X X (𝟙 X) g hd L) → G = F) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
