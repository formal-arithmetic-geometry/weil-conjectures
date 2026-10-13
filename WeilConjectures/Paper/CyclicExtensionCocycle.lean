/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.Algebra.Exact.Basic

/-! # Cyclic extensions and Koszul one-cocycles

Source: Stacks Project, More on Algebra, Tags 05ED and 05EE, and Homology,
Section 010I (blueprint: lem-weil-pbc-cyclic-extension-cocycle).
-/

@[expose] public section

universe u v w z

namespace Paper

/-- Extensions of `A/J` by `P` are represented by admissible Koszul one-cycles.
Source: Stacks Project, More on Algebra, Tags 05ED and 05EE, read on extensions
as in Homology, Section 010I (blueprint: lem-weil-pbc-cyclic-extension-cocycle).

Proof, following the node's five steps:
1. The map from the free module sending `e i` to `f i` kills the relations and
   descends to `μ`, with image `J`. A cycle similarly induces `xhat` on `F/W`.
   Its vanishing on `ker μ` says that every relation `∑ a i * f i = 0` also
   satisfies `∑ a i • x i = 0` (free-module and quotient-module dependency nodes).
2. Projection to `A/J` kills `(x i, -f i)` and descends to the quotient. It is
   surjective. For a representative `(p,a)` in its kernel, write `a = ∑ b i * f i`
   and add the corresponding relations to get `(p + ∑ b i • x i,0)`.
   If `(p,0)` is a relation, admissibility gives `p = 0`. This proves exactness
   (quotient-module, direct-sum-modules and exact-sequence dependency nodes).
3. In any extension, `q (f i • lift) = 0`. Exactness and injectivity of `j` give
   unique `x i` with `j (x i) = f i • lift`. Commutativity gives the cycle
   identities. Applying `j` to any relation proves admissibility (exact-sequence node).
4. The map `(p,a) ↦ j p + a • lift` kills the relations. To lift an element of `E`,
   lift its image in `A/J` to `a` and use exactness on the remainder. For its
   kernel, write `a = ∑ b i * f i`; injectivity of `j` gives
   `p = -∑ b i • x i`, so the pair lies in the relation submodule. The induced
   map is an isomorphism and commutes with the extension maps (quotient-module,
   direct-sum-modules and exact-sequence dependency nodes).
5. Subtracting `f i • m` preserves cycles and the vanishing on relations.
   The map `(p,a) ↦ (p + a • m,a)` sends each relation for `x` to the relation
   for `x'`; its inverse uses `-m`. The first inclusion and the second-coordinate
   projection commute with it (quotient-module and direct-sum-modules nodes). -/
theorem cyclic_extension_cocycle
    {A : Type u} [CommRing A] {P : Type v} [AddCommGroup P] [Module A P]
    (t : ℕ) (ht : 1 ≤ t) (f : Fin t → A)
    (J : Ideal A) (hJ : J = Ideal.span (Set.range f))
    (F : Type w) [AddCommGroup F] [Module A F] (e : Module.Basis (Fin t) A F)
    (W : Submodule A F)
    (hW : W = Submodule.span A (Set.range (fun ij : Fin t × Fin t =>
      f ij.1 • e ij.2 - f ij.2 • e ij.1)))
    (μ : (F ⧸ W) →ₗ[A] A) (hμ : ∀ i, μ (W.mkQ (e i)) = f i) :
    let Z_f : Set (Fin t → P) := {x | ∀ i j, f i • x j = f j • x i}
    let admissible : (Fin t → P) → Prop := fun x => x ∈ Z_f ∧
      ∃ xhat : (F ⧸ W) →ₗ[A] P, (∀ i, xhat (W.mkQ (e i)) = x i) ∧
        ∀ k, k ∈ LinearMap.ker μ → xhat k = 0
    let W_x : (Fin t → P) → Submodule A (P × A) := fun x =>
      Submodule.span A (Set.range (fun i => (x i, -f i)))
    let E_f := fun x => (P × A) ⧸ W_x x
    let iota := fun x => (W_x x).mkQ.comp (LinearMap.inl A P A)
    ∃ pi : ∀ x, admissible x → E_f x →ₗ[A] A ⧸ J,
      (∀ x hx p a, pi x hx ((W_x x).mkQ (p, a)) = Ideal.Quotient.mk J a) ∧
      (∀ x hx, Function.Injective (iota x) ∧ Function.Exact (iota x) (pi x hx) ∧
        Function.Surjective (pi x hx)) ∧
      (∀ (E : Type z) [AddCommGroup E] [Module A E]
        (j : P →ₗ[A] E) (q : E →ₗ[A] A ⧸ J),
        Function.Injective j → Function.Exact j q → Function.Surjective q →
        ∀ lift : E, q lift = Ideal.Quotient.mk J 1 →
        ∃ x : Fin t → P,
          (∀ i, j (x i) = f i • lift) ∧
          (∀ y : Fin t → P, (∀ i, j (y i) = f i • lift) → y = x) ∧
          x ∈ Z_f ∧
          ∃ (hx : admissible x) (theta : E_f x ≃ₗ[A] E),
            (∀ p a, theta ((W_x x).mkQ (p, a)) = j p + a • lift) ∧
            (∀ p, theta (iota x p) = j p) ∧
            (∀ y, q (theta y) = pi x hx y)) ∧
      (∀ x (hx : admissible x) (m : P),
        let x' := fun i => x i - f i • m
        ∃ (hx' : admissible x') (change_iso : E_f x ≃ₗ[A] E_f x'),
          (∀ p a, change_iso ((W_x x).mkQ (p, a)) =
            (W_x x').mkQ (p + a • m, a)) ∧
          (∀ p, change_iso (iota x p) = iota x' p) ∧
          (∀ y, pi x' hx' (change_iso y) = pi x hx y)) := by
  sorry

end Paper
