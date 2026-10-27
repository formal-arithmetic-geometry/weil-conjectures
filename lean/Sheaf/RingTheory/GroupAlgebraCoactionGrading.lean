module

public import Sheaf.AlgebraicGeometry.RingDiagonalizableGroup
public import Mathlib.RingTheory.TensorProduct.Basic

/-! # The grading defined by a group-algebra coaction

Source: Stacks Project, Tag 0EKK, `lemma-complete-reducibility-Gm`, coefficient-projection
proof, generalized to an arbitrary commutative base ring and additive abelian character group
(blueprint: lem-sfb-group-algebra-coaction-grading).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace AddMonoidAlgebra

/-- A counital, coassociative algebra coaction of `R[M]` gives its weight grading.
The submodules have exactly the displayed homogeneous carriers. Every element has a unique
finitely supported homogeneous expansion; the unit and all scalars have degree zero,
products add degrees, and the coaction is the corresponding sum of pure tensors.

Source: Stacks Project, Tag 0EKK, `lemma-complete-reducibility-Gm`, lines 2340–2370;
the same coefficient calculation for arbitrary `R` and `M`
(blueprint: lem-sfb-group-algebra-coaction-grading).

Proof:
1. For each `m`, take the coefficient functional `q_m` on the finitely supported group
   algebra. The balanced tensor universal property defines `C_m(a ⊗ f) = q_m(f) • a`.
   Expand the finite supports of any tensor presentation to reconstruct each tensor
   uniquely as the finite sum of `C_m(x) ⊗ e_m`.
2. Put `p_m = C_m ∘ ρ`. The tensor expansion has finite support. Applying the counit
   gives `a = ∑ p_m(a)` because the counit sends every `e_m` to one.
3. Apply coassociativity and extract the coefficient in the final tensor factor to
   obtain `ρ(p_m(a)) = p_m(a) ⊗ e_m`; thus each coefficient has the asserted weight.
4. Linearity of `ρ` and of `a ↦ a ⊗ e_m` makes every weight carrier an `R`-submodule.
   Steps 2 and 3 give the finite homogeneous expansion.
5. For any other such expansion, apply `ρ` and extract each coefficient. This recovers
   every summand and proves uniqueness, as well as the displayed coaction formula.
6. Since `ρ` is an algebra homomorphism, its unit and scalar images have degree zero.
   Multiplicativity and `e_m * e_n = e_(m+n)` give the product rule.

These are the six elementary steps of the node, using
`def-sfb-ring-diagonalizable-group`, `def-weil-pbc-module-tensor-product`,
`def-weil-pbc-algebra-hom-quotient`, and the tensor-algebra multiplication in
`lem-weil-pbc-algebra-tensor-pushout-universal-property`. -/
theorem group_algebra_coaction_grading
    (R : Type u) [CommRing R] (M : Type v) [AddCommGroup M]
    (A : Type w) [CommRing A] [Algebra R A]
    (ρ : A →ₐ[R] A ⊗[R] AddMonoidAlgebra R M)
    (hcoassoc : ∀ a : A,
      TensorProduct.assoc R A (AddMonoidAlgebra R M) (AddMonoidAlgebra R M)
          (ρ.toLinearMap.rTensor (AddMonoidAlgebra R M) (ρ a)) =
        (Coalgebra.comul (R := R) (A := AddMonoidAlgebra R M)).lTensor A (ρ a))
    (hcounit : ∀ a : A,
      TensorProduct.rid R A
          ((Coalgebra.counit (R := R) (A := AddMonoidAlgebra R M)).lTensor A (ρ a)) = a) :
    ∃ W : M → Submodule R A,
      (∀ (m : M) (a : A), a ∈ W m ↔ ρ a = a ⊗ₜ[R] (single m (1 : R))) ∧
      (∀ a : A, ∃! f : M →₀ A, (∀ m : M, f m ∈ W m) ∧ f.sum (fun _ b ↦ b) = a) ∧
      (1 : A) ∈ W 0 ∧
      (∀ r : R, algebraMap R A r ∈ W 0) ∧
      (∀ (m n : M) (a b : A), a ∈ W m → b ∈ W n → a * b ∈ W (m + n)) ∧
      (∀ (a : A) (f : M →₀ A), (∀ m : M, f m ∈ W m) →
        f.sum (fun _ b ↦ b) = a →
          ρ a = f.sum (fun m b ↦ b ⊗ₜ[R] (single m (1 : R)))) := by
  sorry

end AddMonoidAlgebra
