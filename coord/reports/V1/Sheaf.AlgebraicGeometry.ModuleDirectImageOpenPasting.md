## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.ModuleOpenPasting.moduleDirectImageOpenPasting`
without changing its statement, its coefficient maps, its functors, its adjunctions, or any
public definition. All added constructions and supporting lemmas are private to the item module.

The comparison is the inverse mate of the square assembled from the specified module direct-image
compositors. Its action on the distinguished adjunction-unit coprojections is computed explicitly.
Open sheaf localization, together with the scalar-extension/comap-inverse unit identity, makes
those coprojections bijective. The cartesian fibre-product comparison is invertible, so the
section formula proves that the module mate is an isomorphism. Existing formal mate-pasting laws
then give the successive-open, mixed and identity laws with the specified compositors.
Composition uses the existing module coherence theorem; the degreewise clauses are naturality.

Added private proof imports for the published localization unit formula, scalar-extension unit
coherence, cartesian site comparison, and formal base-change pasting. Updated the item's DAG proof
and proof dependencies to describe this route. No adopted source-library module is changed.
The proof-local irreducibility commands are documented, with their consumers, in
`coord/changes/V1-module-open-pasting-proof-reducibility.md`; public definitions and signatures
are unchanged.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.ModuleOpenPasting.moduleDirectImageOpenPasting`
(node `lem-sfb-module-direct-image-open-pasting`).

Holes closed: 1. Holes added: 0. Holes left in the item module: 0. No split-off statement.
Every new private theorem is proved; every private definition is an explicit construction.

## No longer needed

Removed these private proof imports:

- `Sheaf.CategoryTheory.SheafTensorStructure`.
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`.

The proof no longer separately uses the nodes
`det-def-sfb-sheaf-tensor-structure`,
`lem-sfb-section-ring-lax-pushforward-coherence`,
`lem-weil-pbc-proetale-ringed-open-comparison`, `def-sfb-eta`,
`def-weil-pbc-proetale-operations`,
`lem-weil-pbc-continuous-functor-sheaf-pullback-adjunction`,
`lem-sfb-eta-comp`, or `lem-sfb-eta-id`.
The existing internal module and adjunction API already supplies the specified actions and
compositors; the direct mate calculation proves their section normalization without passing
through a second model of module sheaves or rebuilding coefficient-square coherence.
Their obsolete top-level tool approvals were removed from this node.

These are local proof-dependency removals, not module withdrawals. In particular the public
`ProEtaleOpenRestrictionCounit` import stays because `objectComposition` appears in the public
signatures; no declaration or module is deleted. The affine-space unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and no mathematical error was found. The DAG's eleven-step plan
reconstructed internal-to-sectionwise module transport and coherence already provided by the
published internal module API and formal mate-pasting API. The shorter route retains the exact
section normalization, all actual cartesian-square representatives, both unit constraints and
all degreewise assertions. Identity maps, empty opens and the empty scheme are covered by the
same unit and pullback calculations, with no nonempty hypothesis.

The private formalism is an explicit abbreviation. Generic proved component, mate-unit and
forgetful-compositor lemmas keep the large internal module constructions from being expanded
repeatedly by the kernel. The complete file passed a diagnostic compilation with a reduced
20,000-heartbeat budget in 27.2 seconds; the delivered file uses the project defaults.
No second reader was started, as required by the dispatcher.

## Second reading by V1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
