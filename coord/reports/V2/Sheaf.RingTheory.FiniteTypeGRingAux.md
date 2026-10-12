## What changed

Proved `finiteType_completion_regular`, without changing its signature, by the route of
Stacks 07PV: finite type polynomial presentation, induction on the number of variables,
quotient reduction, and completion descent. The induction uses Mathlib's empty-variable
and finite-successor polynomial equivalences. For the one-variable step, complete a flat
local comparison map, prove its completion map local using the maximal-ideal formula and
commuting square, infer faithful flatness, and apply regular permanence. Then apply the
maximal-ideal G-ring criterion. The final surjective algebra homomorphism identifies S
with the quotient by its kernel.

Added `GRingEquiv` and `PolynomialGRingComparison`, each containing one strict intermediate
statement. Their source and full proof in words are in the docstrings. The original node's
proof and dependencies now follow the Lean proof. The new comparison module imports the
existing statements its proof plan needs.

## Proved and sorry left

`finiteType_completion_regular` (node
`lem-weil-pbc-finite-type-over-g-ring-formal-fibres`) has no sorry.

New remaining sorries:
- `isGRing_of_ringEquiv`, node `lem-weil-pbc-g-ring-ring-equiv`.
- `exists_polynomial_flat_local_regular_completion_comparison`, node
  `lem-weil-pbc-polynomial-g-ring-comparison`.

All three modules compile locally; the dry run checks them on the server and runs the
axiom probe and preflight. The proof still depends on existing unproved library statements;
this is a reduction, not a claim that the full G-ring argument is sorry-free.

## No longer needed

Removed direct imports from the item:
- `Sheaf.RingTheory.RegularBaseChange`.
- `Sheaf.RingTheory.RegularComposition`.
- `Sheaf.RingTheory.PolynomialCompleteLocalFormalFibres`.

Their nodes remain necessary in the new comparison statement's plan. No module is claimed
pruned from the targets' transitive closure. The original node's finite-type Noetherian
step is handled by polynomial Noetherian instances and quotient permanence; the
`lem-weil-pbc-finite-type-algebra-noetherian` dependency is not needed directly here.
Removed from the item's direct proof dependencies:
- `lem-weil-pbc-regular-base-change` (retained by the comparison helper).
- `lem-weil-pbc-polynomial-complete-local-formal-fibres` (retained by the comparison helper).
- `lem-weil-pbc-regular-composition` (retained by the comparison helper).
- `lem-weil-pbc-finite-type-algebra-noetherian` (replaced here by Mathlib instances).

The public imports `GRing` and `Mathlib.RingTheory.FiniteType` remain necessary for the
unchanged statement.

## Where the brief, the DAG or earlier work was wrong

The original plan omits usable interfaces for the polynomial comparison square and
ring-equivalence transport, and does not spell out induction on the number of variables.
These are now explicit. The existing maximal-ideal comparison cannot be applied directly:
it assumes regularity at all maximal local completions, the very assertion needed in the
polynomial step. The new comparison only gives a flat local map with regular composite;
completion descent is proved in the item, rather than hidden in the new statement.

The source file is absent locally; the source proof was read at
https://stacks.math.columbia.edu/tag/07PV. No source was changed. Searches used LeanFinder,
Loogle, and ripgrep over Mathlib and the project. LeanSearch returned Internal Server Error,
recorded as unavailable rather than a negative result.

Edge cases: the induction explicitly handles zero variables and the identity polynomial
presentation. Ring equivalence includes the zero ring (no primes, preserved Noetherianity).
The comparison assertion does not assert existence of a maximal ideal in a zero polynomial
ring: its maximal ideal argument already supplies that hypothesis. It does not assume the
original contraction is maximal in R; it localizes at the prime contraction first.
The item's node is not a unit realization; the unit's statement and steps are unchanged.

## New nodes

`lem-weil-pbc-polynomial-g-ring-comparison` records the bottom and right sides of the
polynomial completion square in Stacks 07PV. It does not conclude regularity of the
original completion map; the item proves that through flat completion and descent.

`lem-weil-pbc-g-ring-ring-equiv` records invariance under ring equivalence, needed in the
zero-variable and successor induction cases and in the final quotient presentation. It
is purely transport, with no finite type ascent conclusion. Both statements were searched
for before being added; no existing interface supplies them.

## Second reading by V2

1. Statement identity: compared the delivered item with the repository version; the target declaration signature is byte-for-byte unchanged. Verdict: pass.
2. Proof checks: compiled all three delivered modules with `lcompile.py`; the target has no `sorry`, and the only remaining sorries are the two named split-off theorems with matching nodes and docstrings. The scratch-copy `#print axioms` probe for all three declarations showed only `propext`, `Classical.choice`, `Quot.sound`, and `sorryAx` from the explicitly open statements. No forbidden declarations were found. Verdict: pass.
3. Split-off statements: checked the two helper statements against their node text, sources, and edge cases (zero-variable polynomial and zero rings); neither weakens the target or duplicates it. Independent LeanFinder search for isomorphism preservation of formal fibres, Loogle search `AdicCompletion, RingEquiv`, and project ripgrep found no existing interface; the nearby maximal-ideal comparison requires the conclusion being sought. Compared the helper construction directly with Stacks 07PV. Verdict: pass.
4. Pruning: removed the three direct imports unused by the final proof and recorded them above; the remaining item imports are used, and the comparison helper retains its stated proof-plan imports. The proof follows the unit route through the comparison, flat completion, permanence, and quotient steps. Verdict: pass.
5. DAG agreement: updated proof, proof dependencies, and proof origin for the item and supplied complete node records for both split-off declarations. Verdict: pass.

Changed after the first reading by adding this second-reading record and explicitly listing all four removed direct DAG dependencies under `## No longer needed`; no Lean source or node statements were altered. The two split-off proofs require substantial localization/completion transport infrastructure and were not closed in this review.
