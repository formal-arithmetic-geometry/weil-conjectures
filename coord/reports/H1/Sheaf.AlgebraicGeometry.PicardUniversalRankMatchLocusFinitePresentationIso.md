## What changed

The existing target theorem now obtains a locally finitely presented rank-match
representative from the new construction theorem, builds maps in both directions
from their characteristic properties, and proves the two inverse equations by
monomorphism cancellation. Its signature and all existing public imports are unchanged.
The construction module is imported only for the proof. Its two proof-dependency
imports are also plain imports: PerfectDirectImageBaseChange and
PerfectLowestCohomologyLocus. No definitions or instances were added or changed.
The existing target node now records the construction dependency and explicit comparison.

## Proved and sorry left

Closed one existing hole, by declaration name:
`AlgebraicGeometry.Scheme.picardUniversalRankMatchLocus_exists_finitePresentation_iso`.
Added one open construction theorem:
`AlgebraicGeometry.Scheme.exists_picardUniversalRankMatchLocus_finitePresentation_core`,
node `lem-sc-picard-universal-rank-match-locus-lfp-core`.
This is a decomposition: one hole closed, one hole added, net zero for these declarations.
The construction is still unproved; the comparison is proved. No other holes were added.
The original worker's duplicate theorem
`picardUniversalRankMatchLocus_locallyOfFinitePresentation_core` was removed before delivery.

## No longer needed

No existing imports were removed. The old target node had empty `proof_deps`, so
there are no old dependencies to list as pruned. The original worker's duplicate
finite-presentation assertion is no longer needed and is not delivered; its new node
and module have been rewritten to state the construction step instead.
No pre-existing library module is claimed as pruned.

## Where the brief, the DAG or earlier work was wrong

The first worker's core assertion duplicated the already stated
`picardUniversalRankMatchLocus_locallyOfFinitePresentation`; that existing theorem
itself uses this item. Taking an identity isomorphism merely moved the same hole.
The original docstring's unconditional clopen rank decomposition also silently relied
on connected fibres. These are not assumed here. The construction docstring now uses
the clopen homogeneous-rank components, excludes mixed-rank fibres, and includes the
empty-fibre component. This is the rank-locus method of Tags 0BDP, 0B91 and 0BDL,
with the rank decomposition adapted to the actual hypotheses.

## New nodes

`lem-sc-picard-universal-rank-match-locus-lfp-core` states only the construction of a
locally finitely presented representing immersion, independent of the given W and j.
It supplies the construction part of the old plan; the target explicitly proves the
comparison part. Its proof docstring explains the rank decomposition, both perfect
rank loci, gluing, mixed fibres, empty fibres, and rank zero. Its node records the
two existing proof dependencies, fresh LeanFinder/Loogle and grep searches, and
a recorded unavailable LeanSearch request. No change record
is needed: no existing statement, definition or public visibility changed.

## Second reading by H1

1. Compared the delivered target with the repository using diff. The theorem signature
   is byte for byte unchanged, as are its public imports. Only its proof and one plain
   proof import changed. The other Lean module and its construction declaration are new.
   Verdict: unchanged existing interface; no accidental visible change.
2. Compiled both modules locally in import order through lcompile.py. The target has
   no sorry; the sole sorry is the complete proof of the named construction theorem.
   No axiom, unsafe, opaque, extern, implemented_by, or hollow definition occurs.
   Scratch copies with #print axioms showed exactly propext, Classical.choice,
   Quot.sound and sorryAx for both declarations. The target depends on the remaining
   construction hole; it is not axiom-free yet.
3. Rejected the original split as a duplicate/restatement. Searched Mathlib with fresh
   LeanFinder, Loogle and grep queries, and searched both library roots.
   LeanSearch returned Internal Server Error; this is recorded without a match verdict. The existing
   rank-match representability theorems require a structure-pushforward isomorphism;
   they do not give this construction under the current assumptions. The existing
   finite-presentation theorem depends on this item and cannot be imported back.
   Checked empty test schemes, empty fibres, zero rank, nonreduced base changes, and
   mixed-rank fibres. The new construction is true by the documented rank-locus argument
   and supplies a distinct part of the plan. Verdict: one genuine construction hole;
   no new object is defined by choosing from an unproved mere existence statement.
4. The proof now follows the plan's construction and uniqueness steps; the comparison
   uses only characteristic properties and monomorphism cancellation. Retained the
   required statement imports and plain construction dependency. No old proof dependency
   was available to prune. Read dag/units/sk-prop-av-cube.json; its realized statement
   and step lists are empty, and this delivery leaves the unit and its route unchanged.
   Verdict: no unit bypass; decomposition, not a completed geometric construction.
5. Updated the existing node's proof, proof_deps and proof_origin to the actual Lean
   comparison. The new node names the new theorem verbatim and carries source, proof,
   dependency, creation, blueprint, Lean and search fields. Its planned proof uses the
   two imported established geometric statements. Verdict: node and Lean agree.

Second reading changed: removed the duplicate local-finite-presentation split; stated
and documented the construction step; replaced the identity isomorphism with an
explicit mutually inverse comparison; corrected the rank-decomposition explanation;
updated both nodes and rewrote this report to count the result as a decomposition.
