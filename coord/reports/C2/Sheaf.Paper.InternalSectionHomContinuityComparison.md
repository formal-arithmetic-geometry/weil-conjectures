## What changed

In `Sheaf.Paper.InternalSectionHomContinuityComparison`, proved
`AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison.scalarTransport_identity`
with its statement unchanged. The proof follows DAG step 7: the ordinary restriction
unitor fixes every section; localization carries this equation to the derived
restriction square; the normalized adjunction equation and uniqueness of left
adjoints identify the extension unitors. Private, proved categorical helpers keep
the concrete ringed-site constructions folded. Added the private proof import
`WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate` for the
localization coherence equations.

Factored the existing resolution-naturality calculation used by
`internalHomRepresentative_computes` into a fully proved private lemma over an
abstract ringed site. Its proof applies naturality directly, avoiding the large
simplifier-generated equality proof. The original representative-comparison
argument and components are unchanged. Set `Elab.async` to its default `true`.
The final profiling run compiled in 55.9 seconds; profiling commands were then
removed before delivery.

## Proved and sorry left

Original holes: 7. Closed: 1, `scalarTransport_identity`. Added: 0. Split off: 0.
All names below are in
`AlgebraicGeometry.ProEtale.ModuleObjectRingedComparison` and realize
`lem-sfb-internal-section-hom-continuity-comparison`.

Remaining unchanged holes:

- `homPresentation_nonempty`
- `internalScalarHom_identity`
- `internalScalarHom_composition`
- `scalarTransport_composition`
- `restricted_hom_transport`
- `internal_section_hom_continuity_comparison`

Every added private helper is fully proved. No definition, public signature, or
previously proved theorem was weakened.

## No longer needed

None. No imports, modules, declarations, or DAG dependencies were removed. The
unit's route is retained. The remaining clauses still require the recorded
presentation, tensor, and scalar comparison dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was disputed. The source of `CoefficientTensorModels`
contains the recently added `monoidal_eq` and `comparison_eq` normalization fields,
but the published compiled environment tested in this session did not yet expose
them. They were not redeclared or replaced. They offer a short route for the
remaining `homPresentation_nonempty`: transport the existing tensor comparison
along equality with the native normalized model, then apply the already proved
`globalHom` evaluation comparison.

## Second reading by C2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
