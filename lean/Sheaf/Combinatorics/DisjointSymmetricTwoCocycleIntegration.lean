module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Disjoint

/-! # Integration of symmetric two-cocycles on disjoint subsets

Source: the agent-written finite-set auxiliary below paragraph (3) of the current
blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`, as recorded in the DAG
(blueprint: lem-sfb-disjoint-symmetric-two-cocycle-integration).
The blueprint does not itself assert this auxiliary algebraic lemma.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Set

/-- A symmetric normalized two-cocycle on disjoint subsets of a finite set is the
multiplicative coboundary of a function equal to one on empty sets and singletons.
Source: agent-written finite-set integration auxiliary below the current blueprint
`sk-thm-sf-ctf-stability-direct-images.proof.md`, paragraph (3)
(blueprint: lem-sfb-disjoint-symmetric-two-cocycle-integration).

Proof plan from the DAG:
1. Induct on the cardinality of `E`, with the assertion quantified over all admissible
cocycles. If `E` is empty, take `b = 1`; the sole equation is the empty-set normalization.
Otherwise choose `x ∈ E`, put `F = E \ {x}`, and restrict `q` to `F`. Its symmetry,
normalization and cocycle identity persist. Induction gives a potential `b₀` on `F`.
2. Define `b(B) = b₀(B)` for `x ∉ B` and
`b(B) = b₀(B \ {x}) * q(B \ {x}, {x})` for `x ∈ B`.
Both arguments of `q` are disjoint. The empty set and singletons away from `x` have
value one by induction; at `{x}` the value is `b₀(∅) * q(∅, {x}) = 1`.
3. For disjoint `U,V` avoiding `x`, the quotient formula is the induction equation.
If `x ∈ V`, put `S = V \ {x}`. Substitution and the induction equation give
`b(U ∪ V) / (b(U) * b(V)) = q(U,S) * q(U ∪ S,{x}) / q(S,{x})`.
The cocycle identity on `(U,S,{x})` identifies this with `q(U,V)`, including empty blocks.
4. If `x ∈ U`, interchange `U,V` and apply the preceding case. Symmetry of `q`,
commutativity of `A` and commutativity of union give the required equation.
Disjointness excludes the case that `x` lies in both blocks. This completes induction.
Only multiplication and inverses are used, without divisibility or torsion assumptions.

Subsets of `E` are represented by `Set E`. The dependent argument of `q` restricts
its domain to disjoint pairs; proof irrelevance makes its value independent of that proof. -/
theorem exists_disjoint_symmetric_two_cocycle_integral
    {ι : Type u} (E : Set ι) (hE : E.Finite) {A : Type v} [CommGroup A]
    (q : (U V : Set E) → Disjoint U V → A)
    (hsym : ∀ (U V : Set E) (hUV : Disjoint U V),
      q U V hUV = q V U hUV.symm)
    (hempty : ∀ V : Set E, q ∅ V disjoint_bot_left = 1)
    (hcocycle : ∀ (U V W : Set E) (hUV : Disjoint U V) (hUW : Disjoint U W)
      (hVW : Disjoint V W),
      q U V hUV * q (U ∪ V) W (hUW.sup_left hVW) =
        q V W hVW * q U (V ∪ W) (hUV.sup_right hUW)) :
    ∃ b : Set E → A,
      (∀ B : Set E, B.ncard ≤ 1 → b B = 1) ∧
      ∀ (U V : Set E) (hUV : Disjoint U V),
        q U V hUV = b (U ∪ V) / (b U * b V) := by
  sorry

end Set
