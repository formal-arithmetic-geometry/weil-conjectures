## What changed

Proved `CategoryTheory.ringedNegativeKoszulBasis_d_succ` in
`Sheaf.CategoryTheory.SignedKoszulSummandDifferential` after correcting its false
intermediate statement. Each erased-index coefficient is the integer sign for
the selected preceding indices times the (m+1)-st power of the rank-one scalar.
The proof establishes the formula in every degree and every tensor length by
induction, using the head factor differential, the two total differential
formulas, unitor naturality, and finite-sum reindexing. All new helpers are private
and completely proved. The private irreducible tensor-inclusion wrapper and
section-local irreducibility attributes keep elaboration from expanding the
recursive degree-indexed construction. No shared definition or attribute changes.

Corrected the left side of the existing
`CategoryTheory.ringedNegativeKoszulSummand_D₂_term` statement in
`Sheaf.CategoryTheory.SignedKoszulSummandTermTransport` to contain the same signed
power; its right side and hypotheses are unchanged. Its existing proof hole
remains. This module is held by P1 (claim since 2026-10-26T18:15Z; the worker saw it
unclaimed): the change is a forced correction of a false statement, see `## Forced adaptations`. The already-proved consumer
`ringedNegativeKoszulSummand_D₂_succ` keeps its exact signature and proof. Its
only direct external importer, `SignedKoszulTensorCoordinates`, needs no change.
Public imports, definitions, target statements, and the blueprint unit route are
unchanged. No imports were added or removed.

Both corresponding nodes record the corrected statements and citer checks; the
basis node records the actual induction proof. Change records:
`coord/changes/signed-koszul-basis-signed-power.md` and
`coord/changes/signed-koszul-term-signed-power.md`.

## Proved and sorry left

The item originally contained one hole, in
`CategoryTheory.ringedNegativeKoszulBasis_d_succ`. Its corrected, source-faithful
statement now has a complete Lean proof; the item contains zero holes. The old
false equality is explicitly repaired, not claimed proved. There are no split-off
statements and no added holes. All private helper lemmas are proved.

The delivery also includes the existing hole in
`CategoryTheory.ringedNegativeKoszulSummand_D₂_term`
(node `lem-cbc-signed-koszul-summand-term-transport`), whose statement is repaired
and whose docstring supplies the scalar-balancing and transport proof in words.
It was present before this delivery and is not a new decomposition.
`ringedNegativeKoszulSummand_D₂_succ` remains proved from the basis theorem and
this existing term-transport obligation. Thus the item has 0 remaining holes and
the two delivered modules together have 1 (before: 2; after: 1).

Validation: both delivered modules compile through `lcompile.py`; the item takes
33.2 seconds in its successful standalone compile. The final combined check compiles term transport in 6.5 seconds, the item in
58.9 seconds, and the unchanged direct importer `SignedKoszulTensorCoordinates`
in 35.7 seconds against both repaired modules. The unchanged importer copy was
removed from the sandbox after validation. The delivery tool performs its independent preflight checks.

## Forced adaptations

`Sheaf.CategoryTheory.SignedKoszulSummandTermTransport` (held by P1): only the left side of
`ringedNegativeKoszulSummand_D₂_term` changes, `ringedKoszulScalar O ⟨…⟩` becoming
`(-1 : ℤ) ^ (I.filter (· < i)).card • (ringedKoszulScalar O ⟨…⟩) ^ (m + 1)`, plus its docstring.
Necessity: the item's `ringedNegativeKoszulSummand_D₂_succ` rewrites with the corrected
`ringedNegativeKoszulBasis_d_succ` and then applies the term theorem summand by summand; against the
old term statement the summands do not match and the proof fails. The old statement was also false
(one factor, m = 1, a_0 = 2: multiplication by 2 against 4), so P1 could not have proved it.
Hypotheses, right side and the remaining `sorry` are unchanged.

## No longer needed

None. No imports, dependency nodes, modules, declarations, or unit steps are
pruned. The proof uses the existing completion model and generic Mathlib tensor
and total-differential APIs; it introduces no public intermediate obligations.
The existing term-transport node remains needed by the summand theorem.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (old signatures, repaired in this delivery): the basis theorem
omitted both the preceding-index sign and the exponent m+1 in Lean, although the
negative factor definition already uses the (m+1)-st power. On the one-point site
with O=Z, one factor a_0=2, m=1, and I={0}, its old statement equates multiplication
by 4 with multiplication by 2. For two factors a_0=a_1=1, m=0, and I={0,1}, the
second erased term must have a minus sign. The term-transport theorem made the
same omission on its left side while its right side already used the signed
power: with K=O[0], q=-1 and the one-factor example it equates multiplication by 2
with multiplication by 4. The two repairs match the existing ordered-tensor
construction and preserve the consumer differential formula exactly. They do not
weaken a conclusion or add a hypothesis. The change records list all declaration
users; both nodes list their sole DAG citer, the summand differential node.

The generalized induction includes the empty tensor and empty subset; neither
requires nonzero scalars, a nonzero ring, or boundedness of the coefficient
complex. No target statement or adopted source-library declaration is changed.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
