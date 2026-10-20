## What changed

Completed the queue's retirement of
Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberForward. Its proved official
twin supplies the affine-chart/ideal-containment argument, and deleted.txt
withdraws the copied module. No source-library file is changed.

Added Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberComparison, proving
AlgebraicGeometry.Scheme.smallStrictHenselizationColimitIso_toBase and
AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint_compat.
The structural-map equality follows from the inverse coprojection equation of the
canonical colimit comparison. The corollary composes the given affine
presentation with Spec of its inverse, then applies the upstream theorem.

The sole direct consumer, Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber,
replaces one private import and one forward-theorem application. Its two public
declaration signatures, its backward proof and all target statements are unchanged.
The original forward node now names the official theorem and exact full-model
signature. The singleton-fibre node's proof records the compatibility step, and a
new comparison node records its fully proved API.

Validation: the comparison and adapted consumer compile cleanly, as do unchanged
copies of both transitive consumers, IntegralFibreSectionLocalLiftAux (16.4 s) and
StrictHenselizationModuleFibreFactorization (38.2 s). Those unchanged copies are
not in the delivery. A separate #print axioms check of the comparison equality,
compatibility corollary and retained singleton-fibre theorem reports exactly
propext, Classical.choice and Quot.sound. Every delivered Lean file is within the
100-column limit. Import-direction checking accepts the upstream dependency.

Change record:
coord/changes/C5-strict-henselization-closed-fiber-forward-retirement.md.

## Proved and sorry left

This is the live queue's zero-hole retirement repair: closed 0 of 0 original
sorries, added 0, split off 0, and left 0 in all delivered Lean files.

The new equality
AlgebraicGeometry.Scheme.smallStrictHenselizationColimitIso_toBase and its corollary
AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint_compat
are completely proved (node
lem-weil-pbc-strict-henselization-small-closed-fiber-comparison).
AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint
and AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_closedPoint_eq
remain completely proved in the adapted consumer. The source declaration
AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_fiber_eq_closedPoint_of_eq
is used unchanged from its official module, via the compatibility corollary.

## No longer needed

Withdrawn module: Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiberForward.
Removed its private import from Sheaf.AlgebraicGeometry.StrictHenselizationClosedFiber.
The copied affine-chart proof, maximal-ideal transport and specialization argument
are no longer needed locally: the existing official forward theorem proves them.
The old private small_toBase proof is retained as the reusable proved public
structural-map comparison in the new module.

No mathematical node or blueprint unit step is pruned. In particular
lem-weil-pbc-strict-henselization-chart-maximal-ideal and its official module remain
needed by the preserved official proof, as do its triple-colimit dependencies.
Every DAG parent of the old forward node is preserved and now reaches its official
attachment. No quarantine archive is deleted or edited. A search of lean/ and
quarantine/ found no other direct importer of the withdrawn module.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed theorem, but the live queue and
coord/retire-items.tsv explicitly assign retirement, and the current source has
zero sorries. The two interfaces use isomorphic small and full colimit models.
A direct import replacement fails because the small-model wrapper and the official
extension both export AlgebraicGeometry.Scheme.strictHenselizationStructuralMap_eq
with different types. The compatibility module resolves this with a proved
structural-map equation and a private upstream proof import, preserving the
consumer's public API. No mathematical assertion is disputed or weakened.

The prescribed searches were run through msearch.py. LeanSearch found generic
colimit comparison results; Loogle and Mathlib grep found
CategoryTheory.Functor.Final.ι_colimitIso_inv. Local source search found the complete
upstream forward theorem and the old private comparison proof. There was no
existing public theorem for this structural-map comparison.

## New nodes

lem-weil-pbc-strict-henselization-small-closed-fiber-comparison records the canonical
structural-map equality and transport of the official forward-fibre theorem.
Its Lean attachment lists both complete proofs in StrictHenselizationClosedFiberComparison.
The source is Categories Tag 04E7 (lemma-cofinal), Étale Cohomology Tag 04HX
(lemma-describe-etale-local-ring), and the existing canonical colimit comparison.
All sources were read locally. The blueprint search for strict henselization
returned the construction and geometric-stalk ancestor, with no separate public
comparison theorem. The node is distinguished from
lem-weil-pbc-strict-henselization-closed-fiber-forward, which proves the full-model
fibre assertion; the new equality compares the two existing structural maps and
uses that assertion only for its corollary. It is also distinguished from
def-weil-pbc-strict-henselization-limit, which defines the small model, and
lem-weil-pbc-colimit-initial-full-subcategory, which gives a generic categorical
cofinality result and does not identify these structural maps. No new hole is left.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
