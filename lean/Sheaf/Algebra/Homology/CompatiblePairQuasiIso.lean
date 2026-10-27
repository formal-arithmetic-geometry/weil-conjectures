module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Abelian.Basic
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact

/-! # Epimorphic compatible-pair maps detect quasi-isomorphisms

Source: Stacks Project, Derived Categories, Tag 0646, lemma-projective-resolutions-exist (3),
and Tag 05T7, lemma-subcategory-left-resolution (1), verification of the downward step.
The unbounded compatible-pair criterion is the generalized-element expansion recorded in
its DAG node (blueprint: lem-trf-compatible-pair-quasi-iso).

## Main declarations

- `HomologicalComplex.compatiblePair_condition`: the chain-map identity on cycles.
- `HomologicalComplex.compatiblePairMap`: the canonical map to the compatible-pair pullback.
- `HomologicalComplex.quasiIso_of_epi_compatiblePairMap`: the unbounded criterion.
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace HomologicalComplex

/-- The chain-map identity with the differential restricted to cycles.
Source: Stacks Project, Tag 05T7, lemma-subcategory-left-resolution (1), the compatible-pair
construction (blueprint: lem-trf-compatible-pair-quasi-iso).

Proof: postcompose both sides with the monomorphism `X.iCycles (n + 1)`. The identities
`toCycles_i` and `cyclesMap_i` reduce the equality to the chain-map identity `a.comm`.
Cancel the cycle inclusion. This supplies exactly the compatibility used to define `e^n`
in the node; it imposes no further hypothesis. -/
theorem compatiblePair_condition {C : Type u} [Category.{v} C] [Abelian C]
    {P X : CochainComplex C ℤ} (a : P ⟶ X) (n : ℤ) :
    a.f n ≫ X.toCycles n (n + 1) =
      P.toCycles n (n + 1) ≫ cyclesMap a (n + 1) := by
  sorry

/-- The canonical map `e^n = (a^n, d̄_P^n)` into
`X^n ×_{Z^{n+1}(X)} Z^{n+1}(P)`.
Source: Stacks Project, Tag 05T7, lemma-subcategory-left-resolution (1), the pullback in the
inductive step; Tag 0646 (3) (blueprint: lem-trf-compatible-pair-quasi-iso).
The two legs are the given chain-map component and the actual differential into cycles. -/
noncomputable def compatiblePairMap {C : Type u} [Category.{v} C] [Abelian C]
    {P X : CochainComplex C ℤ} (a : P ⟶ X) (n : ℤ) :
    P.X n ⟶ pullback (X.toCycles n (n + 1)) (cyclesMap a (n + 1)) :=
  pullback.lift (a.f n) (P.toCycles n (n + 1)) (compatiblePair_condition a n)

/-- Epimorphic compatible-pair maps imply epimorphisms on terms and cycles, isomorphisms
on cohomology, and hence a degreewise epimorphic quasi-isomorphism, without boundedness or
projectivity assumptions.
Source: Stacks Project, Tag 0646, lemma-projective-resolutions-exist (3), expanded from
Tag 05T7, lemma-subcategory-left-resolution (1), verification of the downward step
(blueprint: lem-trf-compatible-pair-quasi-iso).

Proof (the node's generalized-element expansion, with ordinary composition):
1. Given a compatible pair `(y,x)` from any object `B`, form its map to the pullback.
   By `lem-sp-abelian-refinements` (a), epicity of `e^n` lifts this map after an epimorphic
   refinement `p : B' → B`, giving `a^n u = y p` and `d̄_P^n u = x p` simultaneously.
2. For a cycle `y : B → Z^n(X)`, use the pair `(i_X y,0)` in degree `n`.
   Its lift has zero differential, so factors through `Z^n(P)`. Cancel the cycle inclusion
   in `X` to see that it lifts `y p`. The same refinement criterion makes every `z^n` epic.
3. For `y : B → X^n`, first lift `d̄_X^n y` through the epic `z^{n+1}` after an epic
   refinement, then apply step 1 to that compatible pair after a second refinement.
   The composite refinement is epic by cancellation, so every `a^n` is epic.
4. Write `q_K : Z^n(K) → H^n(K)` for the cokernel of `d̄_K^{n-1}`. It is epic by its
   universal property. Naturality gives `z^n d̄_P^{n-1} = d̄_X^{n-1} a^{n-1}` and
   `H^n(a) q_P = q_X z^n` (`def-weil-abstract-derived-category`).
5. Let `k : L → Z^n(P)` be the kernel of `z^n`. Apply step 1 to `(0,k)` in degree `n-1`.
   After an epic refinement `p`, one gets `d̄_P^{n-1} u = k p`, hence `q_P k p = 0`.
   Cancel `p`. By `lem-weil-pbc-abelian-exact-epi-cokernel` (a), the epic `z^n` is a
   cokernel of `k`; thus obtain `g : Z^n(X) → H^n(P)` with `g z^n = q_P`.
6. From step 4, `g d̄_X^{n-1} a^{n-1} = 0`. Cancel the epic `a^{n-1}` from step 3.
   Factor `g` through `q_X` to obtain `h : H^n(X) → H^n(P)` with `h q_X = g`.
   The identities imply `h H^n(a) q_P = q_P`, so cancel `q_P` to obtain one inverse law.
   Also `H^n(a) h q_X z^n = q_X z^n`; cancel `z^n` and `q_X` for the other inverse law.
   Thus every `H^n(a)` is invertible and `a` is a quasi-isomorphism. No upper bound or
   projective lifting property enters any step. -/
theorem quasiIso_of_epi_compatiblePairMap {C : Type u} [Category.{v} C] [Abelian C]
    {P X : CochainComplex C ℤ} (a : P ⟶ X)
    (h : ∀ n : ℤ, Epi (compatiblePairMap a n)) :
    (∀ n : ℤ, Epi (a.f n) ∧ Epi (cyclesMap a n) ∧ IsIso (homologyMap a n)) ∧
      QuasiIso a := by
  sorry

end HomologicalComplex
