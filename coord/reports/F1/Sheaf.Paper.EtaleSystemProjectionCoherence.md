## What changed

Proved `AlgebraicGeometry.Etale.SystemProjection.etaleSystemProjection_coherence`
in `Sheaf.Paper.EtaleSystemProjectionCoherence`, preserving its statement and all
public imports. Added private proof imports of
`Sheaf.CategoryTheory.DerivedExactSquareComposition` and
`Sheaf.Paper.IntegralResidueMatePasting`.

The proof first establishes the sectionwise restriction cocycle and identity,
transfers them through inverse-image mates and exact localization, and pastes the
open and proper factors. Private categorical lemmas then identify the scalar
mates using adjoint uniqueness and prove both equations of the theorem. The
item's node records this route. No dependency module, definition, or public interface changes.

## Proved and sorry left

Closed the one hole in
`AlgebraicGeometry.Etale.SystemProjection.etaleSystemProjection_coherence`
(node `lem-pur-etale-system-projection-coherence`). Added zero holes and zero split-off
statements. No `sorry` remains in the item or any private helper.

## No longer needed

No original Lean import was removed, and no module is withdrawn.
The original proof dependencies
`lem-pur-ringed-coefficient-projection-cocycle`,
`lem-sfb-successive-derived-quotient-normalization`, and
`lem-pur-sheaf-ring-derived-coefficient-adjunction` are unnecessary for this proof:
the normalized data already specifies the relevant comparisons, and direct mate
pasting proves their coherence without specializing an existential ringed model
or using scalar representative formulas. Their modules and declarations remain
untouched. The new node dependency list records the exact-localization and mate
APIs actually used.

## Where the brief, the DAG or earlier work was wrong

The planned argument is valid, but its dependency list was less direct than the
available normalized data and categorical APIs. No statement correction or new
mathematical hypothesis was necessary. The unit record has no realized proof
steps, and this proof retains the stated open/proper and scalar-mate route.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
