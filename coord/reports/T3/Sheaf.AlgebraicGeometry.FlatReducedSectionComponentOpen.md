## What changed

Filled the proof of
`AlgebraicGeometry.isOpen_section_component_of_flat_of_geometricallyReduced_fibers`
in `Sheaf.AlgebraicGeometry.FlatReducedSectionComponentOpen`, preserving its statement
and public imports. The proof follows the existing DAG route: apply local constructibility
(Tag 055P) and generalization stability (Tag 055Q), pull both properties back to the
canonical affine cover, apply the constructible/generalization criterion on each prime
spectrum, and push the resulting open neighbourhoods into the source scheme.
The already proved `Smooth.isOpen_section_component` supplied the same affine-cover
argument; no smoothness hypothesis is used in that topological argument.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.isOpen_section_component_of_flat_of_geometricallyReduced_fibers`
(node `lem-trf-flat-reduced-section-component-open`).

There are zero `sorry`s left in the item and zero added holes or split-off statements.
The proof uses the existing declared generalization lemma
`AlgebraicGeometry.stableUnderGeneralization_section_component_of_flat_of_geometricallyReduced_fibers`,
whose proof remains `sorry` in its own unchanged module. This is a proof from the
assigned dependencies, not an assertion that the transitive proof is axiom-free.

## No longer needed

No dependency nodes or modules are pruned. All seven declared proof dependencies remain
used: local constructibility, generalization stability, affine charts and their qcqs
properties, constructibility, its local-to-global criterion, and the spectral openness
criterion. The canonical affine cover implements the planned affine-neighbourhood step.
No new proof-dependency imports are needed: the original imports already expose the
required declarations.

## Where the brief, the DAG or earlier work was wrong

None. The statement and the proof plan fit the existing declarations, including the
scheme's canonical spectrum charts. There are no changes to definitions, signatures,
other existing modules, or the unit route.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
