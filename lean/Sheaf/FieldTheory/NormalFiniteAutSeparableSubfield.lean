/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.FieldTheory.Normal.Defs
public import Mathlib.FieldTheory.SeparableClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Separable
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.FieldTheory.Normal.Basic

/-!
# Finite separable subfield of a normal extension with finite automorphism group

Source: Stacks Project, Fields, Tags 0BME (2), 0BR4, 09HJ, and 030K; Fundamental Groups,
Tag 0BST, second reduction paragraph
(blueprint: lem-dl-a1-normal-finite-aut-separable-subfield).
-/

@[expose] public section

universe u v

namespace separableClosure

/-- The relative separable closure in an algebraic normal extension with finitely many
base-field automorphisms is finite-dimensional. `Normal k E` includes algebraicity; the
whole extension `E/k` is allowed to be infinite-dimensional.

Source: Stacks Project, Fields, Tags 0BME (2), 0BR4, 09HJ, and 030K; the finite-subextension
inference used in Fundamental Groups, Tag 0BST, second reduction paragraph
(blueprint: lem-dl-a1-normal-finite-aut-separable-subfield).

Proof:
1. Put `G = Aut_k(E)` and `N = |G|`, which is positive since `G` contains the identity.
   By `def-weil-pbc-relative-separable-closure`, the relative separable closure `E_s`
   is a subfield consisting of separable algebraic elements. Every finite list in it
   generates a finite subextension by `lem-weil-pbc-algebraic-generators-finite-extension`.
   Thus finite intermediate fields inside `E_s` exist, including the base field.
2. For any such finite intermediate field `F`, put `d = [F:k]`. The theorem
   `lem-weil-pbc-finite-separable-extension-primitive-element` gives `F = k(α)`.
   By `def-weil-pbc-separable-algebraic-extension`, its minimal polynomial `P` is separable.
   By `lem-weil-pbc-simple-algebraic-extension-power-basis`, the first `d` powers of `α`
   form a basis. Expressing `α^d` in that basis gives a monic annihilator of degree `d`,
   so `deg P ≤ d`; a smaller degree would contradict independence. Thus `deg P = d`.
3. Choose an algebraic closure of `E` using `lem-pc-algebraic-closure-exists-unique`.
   By `lem-pc-separable-polynomial-distinct-roots-alg-closed`, `P` has `d` distinct roots
   there. Normality says `P` splits over `E`; evaluating its linear factorization at any
   root in the closure makes a product zero. A factor is zero, so every root lies in `E`.
4. By `lem-weil-pbc-normal-extension-conjugate-by-automorphism`, each root in `E` is
   `σ(α)` for some `σ ∈ G`; conversely every `σ(α)` is a root because `σ` fixes `k`.
   Hence evaluation at `α` surjects from `G` onto these `d` roots, and `d ≤ N`.
   This conjugacy theorem assumes algebraicity and normality, never finiteness of `E/k`.
5. The degrees of finite intermediate fields inside `E_s` form a nonempty subset of
   `{1, ..., N}`. Choose one, `F₀`, of maximal degree `m`, with basis `b₁, ..., bₘ`.
   For any `a ∈ E_s`, the finite field `F₁ = k(b₁, ..., bₘ, a)` is inside `E_s`, by
   `lem-weil-pbc-algebraic-generators-finite-extension`, and contains `F₀` since the
   `bᵢ` span it. Maximality gives `[F₁:k] ≤ m`. The `bᵢ` remain independent in `F₁`.
   An element outside their span would give `m+1` independent vectors: a relation with
   nonzero last coefficient solves for that element, and a zero last coefficient
   contradicts independence of the `bᵢ`. Thus they span `F₁`, so `F₁ = F₀` and `a ∈ F₀`.
6. Every element of `E_s` therefore belongs to `F₀`; the reverse inclusion holds by
   construction. Consequently `E_s = F₀` is finite-dimensional. No bound on the purely
   inseparable part, or finite-dimensionality assumption on `E/k`, was used.
-/
theorem finiteDimensional_of_normal_of_finite_aut
    (k : Type u) (E : Type v) [Field k] [Field E] [Algebra k E]
    [Normal k E] [Finite (E ≃ₐ[k] E)] :
    FiniteDimensional k (separableClosure k E) := by
  sorry

end separableClosure
