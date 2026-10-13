## What changed

Kept the signature, existing docstring, and public imports of
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_formalGlueingData_prime`
unchanged. Added the proof-only import
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineChartRealization`.

The proof first shows that every generator's principal open lies in U. It proves
that the inverse-image charts cover Y: a prime containing all generators contains
the maximal ideal, hence equals it, contradicting membership in the punctured
spectrum. This argument also handles an empty generator family.

A new geometric intermediate theorem supplies formal data and additive section
identifications on the fixed principal charts, their intersections, and their
completed inverse images. Its four formulas concern arbitrary elements of the
ambient chart and prime modules, before imposing H0 equations. It does not assert
a cover, produce functions on H0, or assert compatible matching families.

The item defines its functions on H0 by projecting to each chart coordinate and
applying the chart section identification. Unfolding H0 membership supplies both
sets of kernel equations. Applying the intersection identification to the
chart/chart equations proves sheaf compatibility. Applying the completed-chart
identification to the prime/chart equations proves the displayed overlap equality.
Both arguments are complete Lean proofs; no global sheaf descent is needed here.

The parent node's proof, proof_deps and proof_origin now follow this argument.
The new theorem has its own module, node, source, and complete proof in words.
No existing statement, definition, visibility, or module outside the item changes.

## Proved and sorry left

Original hole closed (one):
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_formalGlueingData_prime`,
node `lem-sbc-punctured-completion-formal-glueing-data-prime`.

New hole added and left (one):
`AlgebraicGeometry.Scheme.CompletionGluingData.exists_affine_chart_realization`,
node `lem-sbc-punctured-completion-affine-chart-realization`.

This is a decomposition, not an axiom-free proof. Net holes closed: zero. The
remaining geometric hole is the section-module construction on affine charts;
the cover argument and extraction of both H0 compatibilities are proved. There
are no sorries in the item's module and no definitions containing postponed data.

The earlier sandbox's two unlanded statements
`exists_formalGlueingData_prime_data` and
`formalGlueingData_prime_local_compatibility` are removed, not counted as baseline
holes closed. Their module and both node files are removed from this delivery.

Validation: both delivered modules compile with lcompile.py in import order.
The delivery dry run checks their declarations, explicit remaining hole, axioms,
node records, and unchanged existing signature. The first worker stopped after its dry run; the independent second reader
performs the final dry run and delivery.

## No longer needed

No baseline imports, nodes, or modules are pruned. Both public imports are needed
by the unchanged statement. The old proof dependencies
`def-weil-finite-integral-morphism` and `def-weil-pbc-formal-glueing-data` remain
under the affine-chart realization node. The matching-sections and H0 definition
nodes remain direct proof dependencies. Thus all four old dependencies are
accounted for; none has been silently removed from the construction.

Removed from the previous unlanded attempt:
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionFormalGlueingPrimeCore`,
`lem-sbc-punctured-completion-formal-glueing-data-prime-data`, and
`lem-sbc-punctured-completion-formal-glueing-data-prime-local`.
These are not pruning gains against the library baseline.

## Where the brief, the DAG or earlier work was wrong

The earlier local compatibility theorem was false: its arbitrary function r was
related neither to the prime equivalence e nor to the formal transition maps.
For a one-chart cover, sheaf compatibility alone imposes no condition on r, so
it cannot imply equality with a prescribed completed section. This delivery
removes that claim entirely. It does not use it as a disputed premise.

The replacement supplies equations relating the actual section identifications
to alpha and alpha_overlap on every ambient module element. The proof then uses
both H0 equations, which is the relation missing from the earlier attempt.

Read Stacks Tags 0BLH and 05EL and the signatures of the four original dependency
nodes and modules. There is no existing geometric chart-construction theorem
among those dependencies: three are definitions and the fourth defines finite
morphisms. They supply the notions, but cannot by themselves produce section
identifications. The new theorem isolates that construction rather than claiming
that definitions already prove it. Mathlib's affine localization and
pullbackSpecIso APIs are recorded as ingredients for the remaining proof.

Edge cases checked in the construction's proof in words: an arbitrary open U
with each D(f_i) contained in it; an empty index family (only M' and e remain);
empty principal charts and zero chart rings; repeated or zero generators;
non-Noetherian A and nonflat completion maps. Localization and affine tensor
base change need no flatness or Noetherian hypothesis. In the item, t=0 forces U
and Y empty by the same prime-ideal cover argument, without a separate hypothesis.

The unit record `sk-prop-input-spreading` is unchanged. This remains the planned
local affine-chart construction followed by H0 equations; no unit step is bypassed.

## New nodes

`lem-sbc-punctured-completion-affine-chart-realization` is in
`dag/nodes/sec-smooth-base-change/` and is realized by
`Sheaf.AlgebraicGeometry.Morphisms.PuncturedCompletionAffineChartRealization`.
It states the ambient affine section identifications and four universal
restriction formulas, without H0 or a covering assertion. The node includes its
verbatim Lean signature, source-based proof steps, dependencies, blueprint
ancestry, and actual search records. LeanFinder, Loogle, and grep found only
constituent affine/localization APIs; LeanSearch returned Internal Server Error
and is recorded as unavailable. Blueprint searches for formal glueing and affine
charts found no duplicate realization statement. No change record is necessary:
no existing interface changes.


## Second reading by E1

1. **Existing interface: PASS.** Compared the delivered prime module with the
repository using diff. The only changes are its proof body and one plain import
of PuncturedCompletionAffineChartRealization. The existing theorem signature,
docstring, public imports, namespace, universe and visibility are byte-identical.
The other module is new; there are no changed definitions or forced adaptations.

2. **Kernel proof and holes: PASS as a decomposition.** Compiled both modules in
import order with lcompile.py, without errors or warnings. Appended #print axioms
to temporary copies through lcompile.py: both named theorems report exactly
propext, Classical.choice, Quot.sound and sorryAx. There is precisely one explicit
sorry, the named exists_affine_chart_realization theorem. There are no axiom,
unsafe, opaque, implemented_by or extern declarations, and no new definition.
The existential chart data are eliminated inside a theorem proof, never used to
choose arbitrary data for a definition. The cover proof uses hgen and the local
ring maximal-ideal bound correctly. The two calc proofs apply respectively
hh.2 i j and hh.1 i, the actual two H0 equations, with the correct directions.

3. **Split statement and source: PASS.** Read
[Stacks 0BLH](https://stacks.math.columbia.edu/tag/0BLH), proof paragraphs 1--2,
and [Stacks 05EL](https://stacks.math.columbia.edu/tag/05EL), object and H0
formulas. The geometric construction uses only finite inverse images of affine
principal opens, affine localization, and affine tensor base change. It does
not use the Noetherian/flat hypotheses needed by the later algebraization in
0BLH. The containment hf is exactly what allows the principal charts to be
viewed as opens in U. The over condition on D identifies the E-side principal
open with the corresponding completed chart, with the correct structural
C-action. Tested t=0 (only M' and e remain), f_i=0 (zero section/localization
modules), repeated generators, empty Y or E when the supplied D permits them,
and arbitrary U containing the specified principal opens. No missing flatness
assumption arises: affine tensor base change and localization work for arbitrary
ring maps. The new statement omits hgen, the punctured-spectrum hypothesis,
the cover assertion and all H0 matching-family conclusions; it is strictly the
geometric construction step, not a restatement of the item.

Independent searches used different wording: LeanFinder for affine scheme
section-ring localization/restriction/base-change tensor products, Loogle for
pullbackSpecIso, and rg across lean/Sheaf, lean/WeilConjectures, the upstream
AlgebraicGeometry directory and DAG records. They found constituent APIs and
existing downstream formal-glueing comparisons, but no theorem constructing
these formal data. The one remaining hole is not feasible to close in a few
minutes: it requires building the scalar actions, affine identifications and
Data.square/Data.cocycle, not merely applying a known declaration.

4. **Route and pruning: PASS.** Read the matching-sections, FormalGlueing.Data
and H0 modules and sk-prop-input-spreading's realized record. The construction
followed by H0 equations keeps the existing unit route; its realized record is
unchanged. Both public imports of the item occur in the unchanged statement;
its new plain import is proof-only. Both imports of the new module occur in its
signature. All four old proof dependencies are accounted for in No longer
needed: matching-sections and H0 stay direct; finite morphisms and formal data
stay under the geometric intermediate. No baseline node or module is pruned.
The result closes one original hole and adds one smaller hole, net zero.

5. **DAG agreement: PASS.** Checked both node records against their Lean
signatures. The parent proof's three steps match containment/cover, the chart
realization application, and extraction of the H0 equations. Its proof_deps
are the union of those steps' uses. The new node has source, full signature,
chapter/unit, created/lean/blueprint records, searches, and the named remaining
hole. Its construction uses finiteness for affineness, the supplied D for the
completed identification, and the formal Data structure for coherence. The
proof_origin records agree with these source-based routes.

**Second-reading changes.** Expanded the new theorem's natural-language proof
and matching DAG proof step to explain square and cocycle on fractions, the
swap and compare maps, and extension from fractions/pure tensors to all
elements. Added the independent search result to its node. Corrected the report's
first-worker-only delivery wording and added this review. No Lean statement,
proof term, import or hole count changed.
