## What changed
Replaced the submitted unsound auxiliary decomposition with two precise, strictly
smaller intermediate statements in separate new modules:
`Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayLocalizationPoint` constructs a
pointed affine chart isomorphic to the original punctured root cover, and
`Sheaf.AlgebraicGeometry.Morphisms.RootSplitAwayTransportChart` transports the
supplied splitting through that isomorphism to the degree-one product chart.
The target signature and its existing docstring are unchanged. Both new imports in
the target are proof-only. A local unused-variable linter option preserves the
original signature verbatim, including its unused bound indices and `hj`.
The target node now records the two proof dependencies actually used.

## Proved and sorry left
Hole closed: `AlgebraicGeometry.Scheme.root_split_cover_away_divisor_charts`
(1 of the item's 1 original holes), by a decomposition, not a complete proof.
Holes added:
- `AlgebraicGeometry.Scheme.root_split_away_localization_point`, node
  `lem-sbc-root-split-away-localization-point`;
- `AlgebraicGeometry.Scheme.root_split_away_transport_chart`, node
  `lem-sbc-root-split-away-transport-chart`.
Both have complete natural-language proofs and sources in their docstrings. There
are no other holes in the delivery. Net holes closed minus added is -1; this is a
proper two-step decomposition and is not claimed as ledger progress or an axiom-free
proof. The target and both auxiliaries have only propext, Classical.choice,
Quot.sound and the expected sorryAx in their printed axiom lists.

## No longer needed
No original target imports or old proof dependencies were pruned: the old node's
proof_deps were empty. Deleted the worker's new, unsound module
`RootSplitCoverAwayDivisorChartsAux` before delivery. Removed Limits and Pi from the
new localization module and Etale from the new transport module as unnecessary.
These removals do not prune any existing library module. All four original public
imports are preserved because they support the public signature; the two new
auxiliary imports are plain proof-only imports.

## Where the brief, the DAG or earlier work was wrong
The first worker's transport theorem omitted every splitting hypothesis and was
false: with R=S=Q, g=1, d=1, phi=id and Y empty, it asserts that the empty pullback
is isomorphic to Spec Q. The submitted target proof consequently ignored delta,
hdelta, hn and hj. Moreover, merely adding delta is insufficient: an arbitrary
localization of R need not trivialize a cover that splits only over the root cover.
The repaired localization supplies the affine isomorphism e to that root cover and
its over-base identity, and the repaired transport consumes e, that identity,
delta and hdelta. The original localization statement alone was true but did not
supply enough data for the intended argument. New-node records also lacked searches,
verbatim signatures and docstring proofs; these have all been repaired.

## Second reading by C1
1. Compared the delivered target with the repository using diff. The entire original
theorem signature and docstring are byte-for-byte unchanged. Only scoped linter
configuration, two plain imports, and the proof body changed. No definition, target
statement, hypothesis or conclusion changed. Verdict: pass after repair.
2. Compiled all three files through lcompile.py, with no errors or warnings. Searched
for forbidden declarations and holes: only the two public named auxiliary theorems
contain sorry, each as its whole proof. No data definition was added. A scratch copy
with #print axioms for all three declarations showed only the three allowed axioms
and sorryAx. Verdict: pass as a decomposition with two recorded holes.
3. Checked the statements from the top downward and corrected the false transport
claim. The chart construction no longer mentions Y, d or a splitting; transport
requires an actual over-base affine isomorphism and the actual splitting, and no
point or etaleness hypothesis. Thus neither merely restates the target. Small cases:
n=1 gives D(g), n=0 is excluded only in construction; g=0 makes hy impossible;
a point rules out the zero base ring; d=0 makes both transported sides empty.
Mathlib searches via msearch.py used LeanSearch (unavailable), LeanFinder, Loogle
and grep; repository searches used different terms, including root etaleness and
degree-one evaluation. Found basicOpenIsoSpecAway, sigmaSpec and standard-etale
algebra ingredients, but no complete matching theorem. Neither gap is a quick
single-lemma application: localization needs root etaleness/surjectivity, transport
needs pullback/coproduct and evaluation compatibility. Verdict: true, needed,
strictly smaller intermediate statements, with complete docstring proofs.
4. Kept the source's two-step route: pointed affine punctured root chart, then
transport to degree-one charts. Removed unused imports in the new modules. The
unit sk-prop-input-spreading has empty realized statement/step lists and this item
is not a realized unit step; its route is unchanged. No old proof dependency can
be pruned because the original list was empty. Verdict: pass.
5. Matched each new node's statement and verbatim Lean signature, chapter, unit,
source, natural-language proof, search records and creation fields to the Lean.
Updated the existing item's proof/proof_deps/proof_origin to reflect the exact two
applications. Verdict: pass.

Second reading changed: removed the false auxiliary theorem, supplied the missing
root-chart isomorphism and splitting hypotheses, separated the two new statements
into their own modules, repaired the DAG and search records, documented the holes
honestly as decomposition, and removed unused auxiliary imports.

## New nodes
`lem-sbc-root-split-away-localization-point` states the pointed affine chart of the
punctured root cover, including the crucial isomorphism over Spec R. Its source is
the off-divisor branch of Stacks 0EYG specialized by standard basic-open localization.
It is stated in RootSplitAwayLocalizationPoint, with the full construction proof.

`lem-sbc-root-split-away-transport-chart` states transport of the supplied splitting
along that affine isomorphism, followed by the degree-one evaluation/product chart.
It is stated in RootSplitAwayTransportChart, with a full proof including d=0.
Neither new statement changes an existing interface, so no change record is needed.
