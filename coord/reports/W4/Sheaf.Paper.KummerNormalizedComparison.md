## What changed

Filled the three theorem proofs in `Sheaf.Paper.KummerNormalizedComparison`.
`kummerAlternating_additive` proves equality of the component chain maps by
extensionality; both sides in each degree are definitionally the sum of the
natural-transformation components. `kummerCochains_additive` uses the existing
`cechImage_additive` instance and composition of additive functors.
`kummerCochains_term` follows from proved private projection lemmas. First prove
the equality of the evaluated section functors, then the equality of the evaluated
Cech diagram functors. Applying object evaluation to that equality avoids an
expensive kernel conversion between the nested concrete module objects. A generic
alternating-complex projection lemma completes the term equality.

Existing signatures, constructions, public imports and instance registrations
are unchanged. The definitions and the already proved injective-resolution
comparison are retained verbatim. Four proved private helpers are added; no
public declaration or dependency is added. Two file-local irreducibility
commands protect the concrete inverse/direct image functors from expensive
unfolding during elaboration, as in `KummerCechDescent`. They do not change any
exported attribute. A declaration-local unused-section-variable linter setting
preserves the original `kummerAlternating_additive` signature. Temporary diagnostic
heartbeat settings have been removed. Change record:
`coord/changes/W4-kummer-normalized-comparison-proof-context.md`.

## Proved and sorry left

Closed all three existing holes, on node `def-sfb-normalized-kummer-comparison`:

- `AlgebraicGeometry.ProEtale.CondensedRing.kummerAlternating_additive`.
- `AlgebraicGeometry.ProEtale.CondensedRing.kummerCochains_additive`.
- `AlgebraicGeometry.ProEtale.CondensedRing.kummerCochains_term`.

No holes remain in the item, and no holes are added or split off.
The composite-additivity proof uses the existing proved `cechImage_additive`.

## No longer needed

None. No proof imports are added. The existing public imports continue to provide
the published interface; no module or DAG dependency is withdrawn. The node has
no planned proof dependencies and there is no alternative unit route to prune.

## Where the brief, the DAG or earlier work was wrong

No correction is required. The rework row is historical: the item is currently
present in `lean/`, and this delivery starts from that current source rather than
withdrawing or replacing its quarantine archive. The node has no numbered proof
steps; the existing theorem docstrings give the componentwise arguments used here.

The cleaned module is checked by the delivery compiler and axiom probe.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
