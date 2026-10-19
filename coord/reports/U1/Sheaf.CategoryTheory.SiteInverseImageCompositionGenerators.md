## What changed

Proved `CategoryTheory.site_inverse_image_composition_generators` in
`Sheaf.CategoryTheory.SiteInverseImageCompositionGenerators` without changing any existing
statement, definition, visibility or import. Two proved private helpers establish the
coefficient-independent argument and the nested-generator restriction formula.

The proof follows all five existing DAG steps. Compose the constructed sheaf adjunctions;
Mathlib's `Adjunction.leftAdjointUniq` and its unit equation give the comparison. Injectivity
of the composite adjunction's Hom equivalence proves uniqueness and equality detection.
Naturality of the second unit rewrites a nested generator as the composite unit followed by
restriction along the composite arrow. Naturality of the comparison proves normalization;
naturality of the composite unit proves functoriality in the sheaf. Restriction compatibility
is functoriality of the presheaf. Specialize this argument to sets and abelian groups, with
the original filtered-colimit universe restriction instance.

The Mathlib searches used Lean Finder, Loogle and grep through msearch.py, as well as local
searches in Mathlib and both library roots. The five declared dependencies are already
provided by Mathlib; no additional project lemma is needed. Read the Stacks source at
Sites Tags 00VE, 00WX and 03CB, including the composition-of-adjoints proof.

## Proved and sorry left

Closed the one original hole:
`CategoryTheory.site_inverse_image_composition_generators`
(node `lem-trf-site-inverse-image-composition-generators`).

Holes closed: 1. Holes added: 0. Sorries left: none. Split-offs: none.
The two private helpers are completely proved.

## No longer needed

None. No import, declared proof dependency, node or module was removed. The proof uses
the original five Mathlib dependencies and keeps the unit route unchanged.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was necessary. The direct-image composition is definitionally
identified in Mathlib, so no transport by a separately constructed comparison is required.
The nested generator formula only uses units and naturality; it does not require that
sheafified sections admit single representatives.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
