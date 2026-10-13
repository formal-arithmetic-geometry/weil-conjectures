## What changed

Replaced the sorry in `AlgebraicGeometry.Scheme.cechFirstSortingTailCancellation`
with a complete Lean reduction to the unsigned label-deletion correspondence.
The original statement and public import are unchanged. Added proof imports of
`Sheaf.AlgebraicGeometry.AlternatingCechTailDeletionCorrespondence` and
`Sheaf.Combinatorics.SignedFacePermutation`.

The proof identifies the incoming partial permutation with the permutation supplied
by the already proved `Fin.signed_face_permutation`, using injectivity of
`Fin.succAbove`. It proves opposite integer coefficients by `pow_succ` and `ring`,
uses equality of junction maps to cancel the scalar multiples, rewrites the filtered
nested sums as subtype sums, and reindexes by the unsigned equivalence. The private
`sum_filtered` helper is proved entirely from Mathlib.

The new module contains actual subtype abbreviations for the two filtered index
sets and one public theorem. Its theorem has no abelian group, cochain value,
coefficient, sign, or finite sum: it specifies only the combinatorial correspondence
and map identities. Its existence witness is used locally in a theorem proof;
no definition chooses data from an unproved existence statement.

The item node now records the unsigned correspondence and the existing signed-face
node as its actual proof dependencies. The unit and chapter routes are unchanged.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.cechFirstSortingTailCancellation`
(node `lem-pc-alternating-cech-first-sorting-tail-cancellation`).

Added one hole in
`AlgebraicGeometry.Scheme.cechTailDeletionCorrespondence`
(node `lem-pc-alternating-cech-tail-deletion-correspondence`).
This is a decomposition, with one hole closed and one added (net zero holes),
not a claim that the unsigned combinatorics is proved. The coefficient/sign
calculation and the sum-reindexing argument are complete Lean proofs. No sorry
remains in the item's module, in any private declaration, or in any definition.

Both delivered modules compile with `lcompile.py --all`, without warnings.
The new correspondence was checked by explicit finite enumeration on all 1,089
three-valued tuples of lengths 2 through 6 (p=0 through 4), totaling 13,941 matched
pairs. The check verified bijectivity, prefix equality, partial-permutation
restriction, deleted-junction equality, and the signed-face identity. These checks
include all-equal tuples, smallest degree, and the empty last-prefix tail; they are
edge-case checks, not a substitute for the remaining Lean proof. An empty I has
no tuple of length p+2.

## No longer needed

No original imports or modules were pruned. The old direct proof dependency
`def-pc-alternating-cech-sorting-operators` is replaced in the item node by
`lem-pc-alternating-cech-tail-deletion-correspondence` and
`lem-pc-signed-face-permutation`. The sorting-operators node remains a statement
dependency and a transitive proof dependency through the correspondence; its
module remains necessary for the unchanged statement and both index predicates.
No new sign lemma is needed: the library's proved signed-face theorem suffices.

## Where the brief, the DAG or earlier work was wrong

The plan cited only the sorting definitions. It did not provide a Lean interface
for the non-elementary deletion/insertion correspondence. This delivery isolates
exactly that unsigned portion and formalizes the rest. The sign portion already
exists as the proved `Fin.signed_face_permutation`; it need not be reproved or
split into another hole.

Read Stacks Tag 01FM, equation `cohomology-equation-first-homotopy` (the project server),
and its omitted-verification paragraph on the official Stacks page. The source
matches the sorting and partial-sorting definitions; the deletion/insertion proof
is explicitly agent-written because the source omits that verification. No
statement error was found. The local literature source checkout is absent;
the online primary source was used for reading. Blueprint searches for
"tail deletion" and "sorting" found no existing blueprint statement for the
unsigned correspondence. Searches in both Lean roots found the signed-face
lemma but no unsigned correspondence. LeanSearch returned Internal Server Error;
this is recorded as unavailable, not as a no-match verdict.

## New nodes

`lem-pc-alternating-cech-tail-deletion-correspondence`, in
`dag/nodes/sec-picard-framework/`, corresponds to
`Sheaf.AlgebraicGeometry.AlternatingCechTailDeletionCorrespondence` and the theorem
`AlgebraicGeometry.Scheme.cechTailDeletionCorrespondence`. It has the full
unsigned outgoing/incoming index predicates, the four map/position identities,
a complete deletion/insertion proof in words, and actual logged searches of
LeanSearch, LeanFinder, and Mathlib via grep. It stays within `sk-thm-picard-pn`.
No statement or definition changes, forced adaptations, or change records.

## Second reading by S2

1. PASS. Compared the complete item module against the repository with `diff`;
   separately checked that its theorem signature is byte-for-byte identical.
   The only existing-code changes are the proof, two plain proof imports, and a
   proved private sum helper. No existing definition or public import changed,
   and no change record or forced adaptation is required.
2. PASS as a decomposition. Recompiled both modules in import order using
   `lcompile.py --all`, without errors or warnings. Compiled scratch copies
   with `#print axioms`: the correspondence uses `propext`, `Quot.sound`, and
   `sorryAx`; the cancellation uses those plus `Classical.choice`. There is
   exactly one delivered sorry, in the named correspondence theorem. No axiom,
   unsafe/opaque declaration, extern, implemented_by, or hollow definition is
   present. The two index abbreviations construct actual predicate subtypes;
   the equivalence witness is eliminated only within a proposition proof.
3. PASS. Read the outgoing/incoming predicates against `cechStableSort`,
   `cechPartialSort`, and `cechJunction`, and checked the deletion/insertion
   proof, including r=a exclusion, validity of b=a, lexicographic ties, the
   final prefix, p=0, and empty I. Reran the finite enumeration: 1,089 tuples
   and 13,941 pairs satisfy the correspondence and sign identity. The remaining
   theorem is strictly the unsigned combinatorial part: arbitrary cochain
   values, signs, scalar cancellation, and sum reindexing are proved in the
   item. Every clause of its conclusion is used by that proof. Its docstring
   and matching new node contain the source and complete construction argument.
   Independently searched LeanFinder for order-preserving permutation restriction
   with a sorted prefix and increasing complement, Mathlib grep for removeNth/
   sort and permutation restrictions, and both repository Lean roots for the
   sorting predicates. Tuple.sort and insertion/restriction primitives are useful
   ingredients, but no existing declaration supplies this full correspondence.
   Closing the remaining construction is not a few-minute repair.
4. PASS after reporting repair. Checked the sign calculation against the proved
   `Fin.signed_face_permutation`; injectivity identifies its induced permutation,
   and the subsequent coefficient and subtype-sum reindexing arguments are valid.
   Every import is needed, and proof-only imports are plain `import`.
   Read Stacks Tag 01FM, equation the project server and the omitted-verification paragraph
   (https://stacks.math.columbia.edu/tag/01FM). The library's sorting definitions
   agree with that source. The unit `sk-thm-picard-pn` and its `realized` record
   are unchanged; this is a reduction below its level. Corrected `No longer
   needed` to account explicitly for the replaced old direct proof dependency,
   which remains necessary transitively and in the statement. No module is pruned.
5. PASS. Checked both node Lean statements verbatim against their declarations;
   checked proof steps, dependency unions, proof_origin, source, chapter, unit,
   creation and blueprint records. Only permitted proof/Lean fields of the old
   node differ from the repository. The new node records exactly the one open
   theorem and its genuinely smaller argument.

Second-reading changes: corrected dependency accounting in `No longer needed`
and added this independent review. No Lean proof or statement repair was needed.
One original hole is closed and one strictly smaller hole is added: net zero,
with the unsigned correspondence still open, not an axiom-free final proof.
