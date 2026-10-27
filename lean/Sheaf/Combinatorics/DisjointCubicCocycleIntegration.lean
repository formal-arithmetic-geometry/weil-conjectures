module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Disjoint

/-! # Integration of symmetric cubic cocycles on disjoint subsets

Source: the agent-written finite-set integration input below paragraph (3) of the current
blueprint's `sk-thm-sf-ctf-stability-direct-images.proof.md`, as recorded in the DAG
(blueprint: lem-sfb-disjoint-cubic-cocycle-integration). The blueprint itself does not assert
this auxiliary lemma; the cited Moret–Bailly I 2.4.5 original is still WANTED.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace Set

/-- A symmetric normalized cubic cocycle on disjoint subsets of a finite set integrates
without any divisibility or torsion hypothesis on its commutative coefficient group.
Source: agent-written algebraic input below the current blueprint direct-images proof,
paragraph (3) (blueprint: lem-sfb-disjoint-cubic-cocycle-integration).

Proof plan from the DAG:
1. Induct strongly on the cardinality of `E`. For cardinality at most two, every disjoint
triple has an empty block, so take `c = 1`. Otherwise remove a point `x`, obtaining `F`,
and apply induction to the restriction of `t` to `F`, obtaining `c₀`.
2. Put `q(U,V) = t(U,V,{x})`. Symmetry and normalization descend from `t`, and its
four-block identity at `(U,V,W,{x})` is precisely the two-cocycle identity for `q`.
Use `lem-sfb-disjoint-symmetric-two-cocycle-integration` to obtain `b`, normalized on
sets of cardinality at most one, with `q(U,V) = b(U ∪ V) / (b(U) * b(V))`.
3. Set `c(B) = c₀(B)` when `x ∉ B`, and otherwise set
`c(B) = c₀(B \ {x}) * b(B \ {x})`. This is normalized on sets of size at most two.
The cubic formula for triples avoiding `x` is the induction hypothesis.
4. By symmetry the remaining triple is `(U,V,Z ∪ {x})` with all three blocks in `F`.
Substitution and cancellation give its cubic difference as
`t(U,V,Z) * q(U ∪ Z,V) / q(Z,V)`. The original cocycle identity on `(U,Z,{x},V)`,
followed by symmetry, identifies this expression with `t(U,V,Z ∪ {x})`.
Empty blocks are permitted throughout, and no roots are taken.

The dependent arguments of `t` restrict its domain to pairwise disjoint triples.
The two symmetry equalities are the adjacent transpositions, which generate all
permutations of three arguments. Subsets of `E` are represented by `Set E`. -/
theorem exists_disjoint_cubic_cocycle_integral {ι : Type u} (E : Set ι) (hE : E.Finite)
    {A : Type v} [CommGroup A]
    (t : (U V W : Set E) → Disjoint U V → Disjoint U W → Disjoint V W → A)
    (hsym : ∀ (U V W : Set E) (hUV : Disjoint U V) (hUW : Disjoint U W)
      (hVW : Disjoint V W),
      (t U V W hUV hUW hVW = t V U W hUV.symm hVW hUW) ∧
      (t U V W hUV hUW hVW = t U W V hUW hUV hVW.symm))
    (hempty : ∀ (U V W : Set E) (hUV : Disjoint U V) (hUW : Disjoint U W)
      (hVW : Disjoint V W),
      U = ∅ ∨ V = ∅ ∨ W = ∅ → t U V W hUV hUW hVW = 1)
    (hcocycle : ∀ (U V W Z : Set E) (hUV : Disjoint U V) (hUW : Disjoint U W)
      (hUZ : Disjoint U Z) (hVW : Disjoint V W) (hVZ : Disjoint V Z)
      (hWZ : Disjoint W Z),
      t U V Z hUV hUZ hVZ * t (U ∪ V) W Z (hUW.sup_left hVW) (hUZ.sup_left hVZ) hWZ =
        t V W Z hVW hVZ hWZ * t U (V ∪ W) Z (hUV.sup_right hUW) hUZ (hVZ.sup_left hWZ)) :
    ∃ c : Set E → A,
      (∀ B : Set E, B.ncard ≤ 2 → c B = 1) ∧
      ∀ (U V W : Set E) (hUV : Disjoint U V) (hUW : Disjoint U W)
        (hVW : Disjoint V W),
        t U V W hUV hUW hVW =
          (c (U ∪ V ∪ W) * c U * c V * c W) /
            (c (U ∪ V) * c (U ∪ W) * c (V ∪ W)) := by
  sorry

end Set
