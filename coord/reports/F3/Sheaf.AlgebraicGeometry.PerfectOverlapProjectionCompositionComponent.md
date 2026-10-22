## What changed

Restored Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent
from the exact archive named by coord/rework.tsv. Its original compile failed at
line 24: Lean rejects setting [local irreducible] on derivedPullback because the
shared definition is now already irreducible. Removed derivedPullback from that
attribute, retaining the local perfectHomComposition attribute. This is an actual
repair of the assigned compiler error, not a no-op or a withdrawal.

The public theorem perfectOverlapProjectionCompositionComponent and private lemma
combineComponents retain their archived statements and complete proofs. The
public import PerfectOverlapCompositeStageMap is retained. The theorem combines
perfectOverlapCompositeCounitFactor and perfectOverlapTailProjectionComponent
with associativity and Iso.inv_hom_id_assoc, as the node prescribes. Its constructor
equalities still identify sigma', eta' and chi' with the fixed comparisons. Both
Boolean branches, empty or equal opens, and unbounded objects are retained.

After removing redundant imports, lcompile.py compiled the final module cleanly
in 11.8 seconds. A text comparison confirms the theorem signature is verbatim the
archived signature. All Lean lines are at most 100 characters. The normal delivery
will perform the axiom probe and preflight.

Change record: coord/changes/F3-perfect-overlap-projection-component-restoration.md.

## Proved and sorry left

This is a restoration and compiler repair with zero existing holes: 0 of 0 sorries
closed, 0 added, 0 split off, and 0 left. The restored declarations are
AlgebraicGeometry.perfectOverlapProjectionCompositionComponent and the proved
private combineComponents lemma. The node is
lem-pc-perfect-overlap-projection-composition-component. This delivery claims no
new mathematical hole closure. No definition or theorem signature changes.

## No longer needed

Removed four redundant private imports from the archive:

- Sheaf.AlgebraicGeometry.DerivedPullbackComposition
- Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare
- Sheaf.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
- Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence

Their necessary declarations remain accessible through the retained imports. Both
stated proof dependencies, lem-pc-perfect-overlap-composite-counit-factor and
lem-pc-perfect-overlap-tail-projection-component, remain used and directly imported.
No DAG node or module is withdrawn or newly pruned, and the archived consumer
PerfectOverlapCompositeObjectPin remains needed. The DAG proof and proof_deps
already match the preserved proof and therefore require no edits.

## Where the brief, the DAG or earlier work was wrong

The quarantine archive's local reducibility assignment predates the current
irreducible derivedPullback definition. Removing the obsolete assignment repairs
its concrete compiler error; the original proof then compiles without changes.
The absence of the live source was quarantine, not evidence that the theorem
was obsolete. The archive, Lean attachment, dependencies and parent are preserved.

Search before repair used msearch leanfinder (categorical factorization and
inverse-isomorphism cancellation), loogle (CategoryTheory.Iso.inv_hom_id_assoc),
and grep (inv_hom_id_assoc), plus rg over both library roots. Loogle confirms
the cancellation lemma used by the existing combining proof; no replacement of
the two geometric dependencies is required. The unit's own statement and realized
route remain unchanged. No item-specific return is present in coord/returns/F3.md.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
