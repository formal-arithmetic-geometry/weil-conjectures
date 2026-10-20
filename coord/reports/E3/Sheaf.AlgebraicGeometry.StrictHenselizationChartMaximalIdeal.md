## What changed

Retire Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal in favor of its proved
WeilConjectures twin, as assigned in coord/retire-items.tsv. The item is listed in deleted.txt;
its existing DAG node now names the official declaration and records its full affine-colimit
presentation. All three direct consumers import the official chart theorem.

AffineStrictLocalRingComparison, NormalConstantGenericUnit, and
StrictHenselizationClosedFiberForward preserve their existing small-model statements and
use the official result through smallStrictHenselizationColimitIso. Each has a proved private
small_toBase compatibility helper. Ring-equivalence locality and maximal-ideal transport give
the original conclusions. The two ind-etale calls also use the official twin with the
comparison spectrum as their specified scheme isomorphism.

The two intermediate consumers ConstantStrictFibreStalkComparison and
SetsPushforwardStalkStrictHenselization replace their public structural-map wrapper import
by the original upstream small-model module. The forward-fibre module does the same.
The sets proof uses the original existence theorem's choose_spec. This removes the duplicate
structural-map helper from the affected environments. All existing consumer signatures,
definitions, attributes, and visibility are unchanged. No upstream file or target is edited.

Change record: coord/changes/E3-strict-henselization-chart-retirement.md.

## Proved and sorry left

This is a retirement repair of an item with zero holes: proved 0 of 0 sorries; 0 holes added,
0 split off. No sorry remains in the withdrawn item or is introduced in any consumer.
The three private small_toBase helpers and all transport glue are fully proved.
The previously proved affine comparison, generic unit, forward fibre, coefficient comparison,
and set-stalk comparison remain proved.

All five adapted files and the five unchanged intermediate import-chain modules compiled
remotely without errors or warnings. The unchanged direct forward-fibre consumer also compiled separately. All five adapted
modules passed the delivery axiom probes. The dry run passed the final static checks
and server preflight with review class CODEX.

## No longer needed

Withdraw the duplicate module Sheaf.AlgebraicGeometry.StrictHenselizationChartMaximalIdeal.
Its three imports in AffineStrictLocalRingComparison, NormalConstantGenericUnit, and
StrictHenselizationClosedFiberForward are replaced by the official twin. No remaining
source imports the withdrawn module.

The two first consumers also remove their private imports of
Sheaf.AlgebraicGeometry.StrictHenselizationAffineChartIndEtale and use the official twin.
The forward-fibre, coefficient-comparison, and set-stalk modules remove the public import of
Sheaf.AlgebraicGeometry.StrictHenselizationStructuralMap in favor of its original upstream
module, avoiding the same-name helper clash. Those two other Sheaf modules still have
other consumers and are not withdrawn by this packet.

The chart node and its mathematical dependencies remain: the official theorem still uses
the etale chart/triples comparison and strict-henselization triples. No node is deleted,
no unit statement or proof step is bypassed, and no unused mathematical dependency is
claimed as pruned. The original chart node remains available to all unfinished DAG parents
through its official Lean attachment.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes proving holes, but the current assigned row is a zero-hole
retirement, even though recent J3/J2 deliveries repaired the old copy's proof. Repeating that
proof would leave the assigned duplication unresolved. The official twin changes the ring
presentation from the small representative colimit to the full affine-neighbourhood colimit;
substitution of its import alone does not preserve the old consumer types.

The initial direct-import compile exposed the structural-map helper collision. The explicit
comparison proof resolves the presentation change, while the two intermediate import repairs
remove the conflicting wrapper from these environments. No held module is edited.

Read Stacks etale-cohomology.tex, lemma-describe-etale-local-ring (04HX), and algebra.tex,
lemma-strict-henselization-different (04GW) and lemma-strict-henselization (04GP), especially
its extended-maximal-ideal clause. The canonical colimit comparison respects every leg;
therefore it respects the structural map. The geometric point guarantees a nonempty
cofiltered representative category, including field and nonreduced-chart cases. The
sk-thm-p1 unit route is preserved.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
