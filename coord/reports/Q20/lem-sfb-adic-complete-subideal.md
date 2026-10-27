## Worker report

Stage 2, group Q20, 2026-10-23. The module
`Sheaf.RingTheory.AdicCompleteSubideal` states
`IsAdicComplete.of_fg_subideal`, with its sole proof `by sorry`.
The node is Stacks Algebra Tag 090T, `lemma-complete-by-sub`, specialized to `M = A`.
I read the full statement and proof at algebra.tex:22776–22806 and the preceding
Tag 090S argument. No correction, new notion, dependency repair or statement dispute
was necessary. Only the item's `lean` field changes; its accepted stage-1 split stays intact.

Every hypothesis and conclusion matches as follows:

- A commutative ring: `(A : Type u) [CommRing A]`, with `universe u` explicit and unrestricted.
- Two ideals in A: `(L K : Ideal A)`; being ideals of A already expresses containment in A.
- The containment L ⊆ K: `(hLK : L ≤ K)`, allowing equality.
- Finite generation of L: `(hL : L.FG)`. Mathlib's `Ideal.FG` in
  `Mathlib.RingTheory.Finiteness.Defs` is literally existence of a finite set with ideal span L.
  This is equivalent to the node's finite list of generators, including the empty list.
- K-adic completeness: `[IsAdicComplete K A]`, with A a module over itself.
- L-adic completeness: `IsAdicComplete L A`, with the same ring and its self-module action.
  This asserts both separatedness and completeness, not merely surjectivity.

The only statement dependency, `def-weil-pbc-adically-complete-ring`, records
`IsAdicComplete` in `Mathlib.RingTheory.AdicCompletion.Basic`. I read its docstring,
class signature and `AdicCompletion.of_bijective_iff`: it is exactly bijectivity of
`AdicCompletion.of I A : A → AdicCompletion I A`, so it includes the intersection-zero
condition in the node. The module publicly imports this recorded module and the finite
generation definition module. The other proof dependency,
`lem-sfb-adic-surjectivity-from-principal-generators`, currently has no Lean record or
Mathlib match; it is not needed to state this theorem, so there is no import yet.
Its role and all four node proof steps appear in the theorem docstring, for stage 3.
No additional statement dependency or arbitrary construction is needed.

Edge cases checked before writing: L = 0 (empty generators) is the discrete completion;
L = K gives the original completeness when L is finitely generated; K = 0 forces L = 0;
nilpotent ideals and zero divisors require no cancellation in the tail-sum proof;
the zero ring is permitted by `CommRing`; K = A forces A to be the zero ring under the
separatedness hypothesis, so that case is included too. The larger ideal need not be
finitely generated. No Noetherian, local, domain, nontrivial-ring or positive generator
count hypothesis is introduced. Index n = 0 in Mathlib adds only the trivial A/A coordinate
to the source's limit over n ≥ 1, leaving completeness unchanged.

Searches for an existing statement, performed through the prescribed `msearch.py Q20
lem-sfb-adic-complete-subideal` wrapper:

- `leanfinder`, query `A commutative ring complete for an ideal K is complete for every
  finitely generated ideal L contained in K`: eight hits on `IsAdicComplete`, its
  precomplete/Hausdorff projections, adic-topology equivalences, henselianity and
  Jacobson containment. None transfers completeness to a finitely generated smaller ideal.
- `loogle`, query `IsAdicComplete, Ideal.FG`: three hits,
  `AdicCompletion.isAdicComplete`, `.isAdicComplete_of_fg`, `.isAdicComplete_self`.
  These assert completeness of an adic completion, not the requested transfer on A.
- `leansearch`, query `Completeness for an ideal implies completeness for a finitely
  generated smaller ideal`: eight hits, the completeness classes and constructors,
  finite generation in Noetherian rings and `Ideal.FG`; no exact theorem.
- `grep`, query `of_le|mono|subideal|090T`, subdirectory `RingTheory/AdicCompletion`:
  25 hits on monotonicity within proofs, Noetherian separatedness and completion
  ring maps; none is this statement. I read the candidate `isAdicComplete` signature
  in Completeness.lean and the Basic.lean completeness/bijectivity interface.
- Direct `rg` of `lean/WeilConjectures` for `IsAdicComplete`, subideal and containment
  names, and for this node id; likewise `lean/Sheaf`. The closest upstream result is
  `IsAdicComplete.of_le_maximalIdeal` in
  `WeilConjectures.RingTheory.CompleteLocalSubideal`, which requires Noetherianity,
  locality and maximal-ideal completeness. I read its full signature and docstring.
  The private helper `complete_subideal` in
  `WeilConjectures.AlgebraicGeometry.Morphisms.CompletedQuotientCoverLift` has the same
  extra restrictions. Neither states the current theorem. The proposed full name
  `IsAdicComplete.of_fg_subideal` has no occurrence in Mathlib, project source, or
  `dag/lean_names_upstream.json`. This node id has no source declaration match.

Verification: prescribed `scompile.py` compiled this module as both its sandbox module
and `Sheaf.RingTheory.AdicCompleteSubideal`, with exit 0 and no diagnostics. All binders
are explicit and `set_option autoImplicit false` is enabled. The theorem has no helper
axioms, definitions, local instances or file-local notation. The JSON Lean statement is
copied verbatim from the declaration signature. The final dry run uses `deliver2.py`.

## Second reading by Q20

Direct-delivery self-review by the dispatched worker; no other agent was started,
as required by the dispatcher. The maintainer supplies the independent review.
I reopened the current node, dependency record, source and completed Lean file and
checked the signature clause by clause: `A : Type u` with `CommRing A` is the source
ring, `L K : Ideal A` gives its two ideals, `hLK : L ≤ K` has the correct direction,
`hL : L.FG` is on the smaller ideal only, the instance is `IsAdicComplete K A`, and
the conclusion is `IsAdicComplete L A`. The finite-generator existential is the
standard `Ideal.FG`, including rank zero. The class uses the ring as its own module;
`of_bijective_iff` confirms both surjectivity and injectivity. The proof docstring
contains separatedness, the principal compatible family, the finite tail-sum argument,
and finite-generator assembly through the existing 090S DAG node. Its latter node
is unstated and therefore has no module import. No mismatch or correction was found.
The only saved sorry belongs to the exact matching DAG theorem. I also checked that
all Lean lines have at most 100 characters and the item differs only in `lean`.
