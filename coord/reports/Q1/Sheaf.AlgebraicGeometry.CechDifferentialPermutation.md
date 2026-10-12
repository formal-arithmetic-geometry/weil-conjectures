## What changed

Proved `AlgebraicGeometry.Scheme.cechDifferential_permutation` without changing its
signature. The proof expands the differential, reindexes by the given permutation,
applies the cochain transformation law to each deleted face, and combines restrictions
using functoriality and thinness of the category of opens.

Added `Sheaf.Combinatorics.SignedFacePermutation`, containing the proved theorem
`Fin.signed_face_permutation`. It constructs the induced deleted-index permutation
from Mathlib's cycles and `Equiv.removeNone`, then proves the face and sign identities.
The target imports this module privately because only its proof uses it.

Removed the proposed `CechDifferentialPermutationAux` module and its proposed expansion
node from the delivery. They were absent from the repository; nothing is deleted from
the library. The expanded theorem merely restated the original hole after unfolding.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.cechDifferential_permutation`
(node `lem-pc-cech-differential-permutation`), 1 of 1 original holes.

Holes added: none. Sorries left in delivered modules: none. The added theorem
`Fin.signed_face_permutation` (node `lem-pc-signed-face-permutation`) is fully proved.
This is a proof, not a decomposition. Relative to the baseline this closes one hole
and adds zero; the maintainer's pinned ledger determines project-wide closure totals.
Both declarations' explicit `#print axioms` checks report exactly `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx`.

## No longer needed

No baseline import or old proof dependency was removed: the original
`def-weil-pbc-site-cech-complex` dependency remains used. No baseline module is pruned.
The refused expansion module/node were never in the library and are excluded from
this repaired delivery.

## Where the brief, the DAG or earlier work was wrong

The earlier expanded signed-face theorem had the same hypotheses and conclusion as
the original theorem after unfolding `differentialValue`. It isolated no strictly
smaller argument and closed no mathematical hole. The earlier report's claim of an
intermediate reduction was therefore rejected on second reading.

The genuine combinatorial step could be proved using the pinned Mathlib's
`cycleRange_succAbove`, `sign_cycleRange`, `map_equiv_removeNone`,
`optionCongr_sign`, and `sign_permCongr`. Searches found no existing theorem with
exactly the deleted-index statement. The online Loogle result
`sign_decomposeFin'Symm` is absent from the pinned local Mathlib; it was not used.
LeanSearch returned a service error, recorded as unavailable rather than no match.

## New nodes

`lem-pc-signed-face-permutation`, in
`dag/nodes/sec-picard-framework/lem-pc-signed-face-permutation.json`, records the
fully proved deleted-index permutation and sign identity. Its source is the
signed-face calculation implicit in Stacks Tag 01FG
(https://stacks.math.columbia.edu/tag/01FG), expanded with Mathlib's cycle and
option-permutation lemmas. Its declaration has a complete natural-language proof
in its docstring. There are no change records because no existing interface changed.

## Second reading by Q1

1. Compared the delivered target module with the repository using `diff` and an
   exact signature comparison. Verdict: the existing declaration's signature is
   byte-for-byte identical; no existing definition or visibility changed. Only
   the proof and one private proof import changed. No change record is needed.
2. Compiled both modules locally in dependency order with `lcompile.py`, without
   errors or warnings. Scanned for `sorry`, `axiom`, `unsafe`, `opaque`,
   `implemented_by`, and `extern`: none occur in delivered Lean. Explicit axiom
   checks on an isolated scratch copy show only the three permitted axioms for
   both declarations. All local data are concrete Mathlib constructions, with
   no choice from an unproved existence theorem. Verdict: complete proofs.
3. Rejected the expanded restatement, removed its undelivered module/node, and
   replaced it with a proved combinatorial lemma. Reviewed its construction and
   sign orientation and checked all 5,039 cases with n = 0 through 5, including
   the empty remaining index set and deletion at either endpoint. The original
   p = 0 case is covered; empty I gives no tuple t, and repeated tuple entries
   need no extra hypothesis. Repeated searches with LeanFinder, Loogle, grep,
   and LeanSearch (unavailable) and searched both library roots. Verdict: the
   new statement is true, needed, strictly smaller, and not an existing theorem;
   there are no split-off statements left with sorry.
4. Read the proof from the target downward. It uses the direct signed-face route
   and existing Mathlib tools, with only the finite-index calculation isolated.
   All imports serve signatures or proofs, and proof-only imports are private.
   The original proof dependency remains used, so the pruning list is complete.
   Read `dag/units/sk-thm-picard-pn.json`: this below-unit repair retains the
   unit's Cech comparison route and changes no realized field. Verdict: shortest
   direct route found, with no departure from the unit or chapter route.
5. Updated the target's proof steps, proof_deps, and proof_origin to match the
   actual summand reduction. The new node records its exact Lean signature,
   construction and sign steps, source, three search kinds, creation metadata,
   blueprint origin, chapter, unit, and Lean record. proof_deps is the union of
   each node's step uses. Verdict: DAG and Lean agree.

Second reading changed: removed the tautological expanded sorry, proved the
combinatorial deleted-index identity and the complete Cech theorem, updated the
nodes, and corrected the progress report. No original statement changed.
