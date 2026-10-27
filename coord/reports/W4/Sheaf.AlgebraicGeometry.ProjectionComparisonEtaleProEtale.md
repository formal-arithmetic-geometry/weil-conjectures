## What changed

Filled the three definitional interface lemmas by reflexivity. Proved the projection
comparison using the existing fixed-coefficient derived tensor compatibility and
`CategoryTheory.Adjunction.map_rightAdjointProjectionMap_comp_mateEquiv`.
The proof constructs the common natural transformation, identifies its tensorators
with the published comparison tensorators, and proves that its unbounded mate at
each bounded-below input is exactly the displayed normalized bounded-below mate.
The item uses the existing coherence helpers, exposed in their owning module;
all remaining local helpers are private and proved. Existing target signatures stay
unchanged. The coherence module publicly imports the owner of ComparisonCompatible
because its exposed theorem signature uses that predicate. The node records the
shorter fixed-coefficient proof route.
Preflight requested a record for the proof-local opens and irreducibility settings:
`coord/changes/W4-projection-comparison-proof-settings.md`. Its consumer review
finds no changed public statement or definition and no required adaptation.

## Proved and sorry left

Closed four original holes:

- `AlgebraicGeometry.ProEtale.sfbProjectionComparisonAdmissible_iff`.
- `AlgebraicGeometry.ProEtale.sfbProjectionComparisonSource_eq`.
- `AlgebraicGeometry.ProEtale.sfbProjectionComparisonTarget_eq`.
- `AlgebraicGeometry.ProEtale.projection_comparison_etale_proetale`.

No holes added or split off. No `sorry` remains in the delivered module. All four
belong to `lem-sfb-projection-comparison-etale-proetale`. The adapted coherence
module also has zero holes. Remote `lcompile.py --all` compiled both files cleanly
(coherence 59.1 seconds; projection comparison 42.1 seconds).

## No longer needed

Removed the private proof imports `Sheaf.Paper.ProjectionMateExact`,
`Sheaf.Paper.RingedExchangeTensorCoherence`,
`Sheaf.CategoryTheory.RingedToposMorphism`, and
`Sheaf.AlgebraicGeometry.ProEtaleConstantRingMap`.
The proof no longer needs `lem-sfb-etale-proetale-ringed-square-realization`,
`lem-sfb-constant-module-derived-projection-identification`, or
`lem-weil-pbc-ringed-exchange-tensor-coherence`: the source library already proves
the tensor-compatible square for the actual fixed-coefficient derived functors,
and the general projection-mate identity applies directly to them. Likewise
`lem-weil-pbc-ringed-projection-mate-exact` is unnecessary as a proof tool, because
the published etale/pro-etale projection maps are definitionally the corresponding
right-adjoint projection maps. Removed the two obsolete top-level tool approvals
for ringed coherence and ringed projection exactness. Existing public imports are
preserved; these statements about the proof route do not claim their modules have
left the whole library's import closure. No source-library declaration is removed.

The repair removes the duplicated `comparisonCompatible_transport`,
`comparisonPullback_transport`, `tensorTransport_app`, `comparison_tensor_app`,
`comparison_tensor_compatible`, and `supportComparison_eq` from the item. It also
removes its private copies of `tensorTransport` and `comparisonTensorNatIso`.
The item now reuses `comparisonTensorNatIso`, `comparison_tensor_app`,
`comparison_tensor_compatible` and `supportComparison_eq` from their existing owner.
The direct proof import of `LowerStarProjComparison` is no longer needed here.

## Where the brief, the DAG or earlier work was wrong

The planned detour through ringed-module realizations is unnecessary: the source
library has the fixed-coefficient tensor-compatible comparison and the categorical
projection-mate identity. The bounded-below normalization still requires proof;
its inclusion maps cannot be replaced by an arbitrary endpoint isomorphism. The
new local proof derives that normalization from the existing specified counit
identity. No statement or definition was repaired, and the unit route is kept.

The returned packet copied six proved private lemmas from
`Sheaf.SixFunctors.ComparisonOpenTensorCoherence`. They were inaccessible to an
importer, but copying them was still a duplicate proof. The repair exposes the
existing concrete tensor API and support-site identity in place, together with
the explicit tensor transport construction used by the public definition. The
six duplicate lemmas and both duplicate definitions are removed from the item.
The generic compatibility transport and the remaining transport lemmas stay
private in the owner. There are no additional holes and no forced adaptations.
The interface change and all downstream users are recorded in
`coord/changes/W4-comparison-tensor-api.md`. The owner is unclaimed.

## Second reading by W4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
