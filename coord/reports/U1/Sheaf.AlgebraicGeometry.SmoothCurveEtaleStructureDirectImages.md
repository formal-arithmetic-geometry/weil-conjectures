## What changed

Prove the item theorem from the existing flat-curve derived model, a proved localized
splitting-to-affine-edge adapter, and a unit-coefficient realization adapter. Keep the
item theorem's signature, its four local-coefficient definitions and its public imports
unchanged. The degree-zero argument uses the canonical proper-flat structural map.

`CurveAffineEdge` proves the localized splitting and flat unit base-change argument.
`UnitAffineCohomologyEtaleRealization` combines two distinct normalization results with
the existing general affine realization theorem. The two remaining results are ordinary
affine comparison transport through pullback symmetry and structural scalar normalization
of an already given coherent realization. Their modules contain exact statements,
sources and complete proofs in words. They retain no properness, smoothness, curve,
Noetherian or finite-local-freeness hypotheses.

The experimental changes to existing comparison and derived-evaluation dependencies
were discarded. No existing dependency definition, public import or signature changes.
No adopted source module is changed. The lengthy complete proof attempt remains in
sandbox scratch notes; the delivery contains only the two explicitly named remaining
steps, with no partial proofs hidden inside definitions or private helpers.

## Proved and sorry left

Closed the one item hole:
`AlgebraicGeometry.Etale.smooth_curve_etale_structure_direct_images`.
The new `AlgebraicGeometry.exists_curve_coherentEdge` and
`AlgebraicGeometry.Scheme.Modules.exists_unitAffineCohomologyEtaleRealization`
are proved from their named dependencies.

Added two holes, each in its own module, with proof exactly `by sorry`:

- `AlgebraicGeometry.Scheme.Modules.exists_unitAffineComparisonTransport`
  (`new-unit-affine-comparison-transport`): transport the ordinary comparison family,
  with linearity and naturality, to the oppositely ordered fibre product.
- `AlgebraicGeometry.Scheme.Modules.exists_unitRealizationScalar_of_coherentAction`
  (`new-unit-realization-scalar-normalization`): normalize a given coherent realization
  with its coherent class action and linearity to actual structural functions.

This is a decomposition: one original hole closed and two strictly separate lower
holes added, not a claim of net hole reduction. The item and both combining adapters
contain zero holes. The delivery has exactly two holes in total.

Validation: all five delivery modules compile through `lcompile.py`. The first full
check compiled both remaining statements and both combining adapters. Its item error
was repaired by explicitly supplying the edge-cohomology quasi-coherence and finite-free
instances from the model's proofs; the item then compiled separately. The original
item signature and public-import list were checked verbatim against the shared source.
All new node Lean statements match their declarations; every referenced node exists.

## No longer needed

The following old direct proof imports have been removed from the item module:

- `WeilConjectures.AlgebraicGeometry.SchemeDerivedBaseChangeMap`
- `WeilConjectures.AlgebraicGeometry.DerivedModuleBaseChangeMap`
- `WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf`
- `Mathlib.AlgebraicGeometry.Sites.Etale`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `WeilConjectures.AlgebraicGeometry.DerivedDirectImageCompositionUnbounded`
- `Sheaf.AlgebraicGeometry.GlobalSectionsGeomConnected`
- `WeilConjectures.AlgebraicGeometry.TensorPullbackAdjunction`
- `WeilConjectures.AlgebraicGeometry.TensorPullback`
- `WeilConjectures.AlgebraicGeometry.DerivedAdjoint`
- `WeilConjectures.AlgebraicGeometry.EtaleQuasiCoherentDescent`
- `Sheaf.AlgebraicGeometry.FlatDerivedStructureUnit`
- `WeilConjectures.AlgebraicGeometry.Cohomology.EulerChar`
- `Sheaf.AlgebraicGeometry.PerfectDegreeZeroFibreCriterion`
- `Sheaf.AlgebraicGeometry.PerfectFiniteFreeResidueModel`
- `Sheaf.AlgebraicGeometry.QcoherentCohomologyComparisonPullback`
- `WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing`
- `Sheaf.AlgebraicGeometry.LeraySpectralSequence`
- `Sheaf.AlgebraicGeometry.AbelianHigherDirectImagePresheaf`
- `WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.PerfectBaseChange`
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap`
- `WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMapFunctorial`
- `WeilConjectures.AlgebraicGeometry.DerivedBaseChangeHorizontalPasting`

These are direct-import removals, not withdrawals of their declarations. The retained
flat-curve and realization lemmas still use some of this theory internally.
No adopted source declaration or DAG node is removed. No unit route is bypassed.
The old direct use of the geometric H0 criterion is subsumed by the already stated
proper-flat structural-map theorem. The rank-one algebra detour in the old degree-zero
plan is unnecessary because that theorem proves invertibility of the canonical map.

The item no longer has these direct proof edges:
`def-weil-proper-morphism`, `def-weil-pbc-scheme-conventions`,
`lem-pc-h0-geom-connected`,
`lem-weil-pbc-coherent-affine-base-change-edge-naturality`,
`lem-weil-pbc-affine-cohomology-etale-module-realization`,
`lem-weil-pbc-qcoherent-cohomology-comparison-pullback`, and
`lem-weil-pbc-affine-etale-site-topos`.
The property definitions remain available to the statement; the affine edge and
realization are used through the new adapters. The separate geometric H0 criterion,
degree-zero coherent comparison, and affine-site detection are not used by the new
degree-zero argument. This does not assert that those modules are globally unreachable.

## Where the brief, the DAG or earlier work was wrong

The affine edge uses X times_S T and its first projection for the coefficient;
affine realization uses T times_S X and its second projection. Their hypotheses do
not match definitionally. Pullback symmetry must transport the ordinary cohomology
comparison, its scalars and its restriction square. In addition, the edge's
section-normalized tensor adjunction must be identified with the adjunction selected
from the normalized existence theorem. These are the ordinary comparison-transport step.

The coherent unit coefficient is canonically isomorphic to actual structural functions,
but that alone does not supply the raw scalar formula. Coefficient naturality of raw
restricted evaluation and canonical higher-image classes is needed. The second remaining
statement assumes the coherent realization and its exact action equations, so it does
not restate the first remaining result or the item theorem.

The original long proof attempt reached both arguments but has unresolved Lean
conversions at the factor-order/naturality and coefficient-evaluation interfaces.
These two mathematical results are stated separately; existing dependency proofs and
definitions are preserved. Empty schemes and zero groups satisfy both statements:
all transport maps remain isomorphisms, and all equations retain their meaning.

## New nodes

`new-curve-split-affine-coherent-edge`, module `CurveAffineEdge`, records the proved
passage from localized structural splitting to the coherent affine edge, with pinned
unit tensor counits and flat derived base change.

`new-unit-affine-comparison-transport`, module `UnitAffineComparisonTransport`, is the
remaining ordinary cohomology transport through canonical pullback symmetry. It asserts
no etale higher-image realization or higher-image module action.

`new-unit-realization-scalar-normalization`, module `UnitRealizationScalarNormalization`,
is the remaining coefficient normalization of a given coherent realization. Its
hypotheses are the action and linearity equations, not the affine comparison family.
Its definitions spell out the actual structural coefficient, raw maps and scalar formula.

`new-unit-affine-cohomology-etale-realization`, module
`UnitAffineCohomologyEtaleRealization`, combines the preceding two results with existing
affine cohomology etale realization. No definition change record is needed: all existing
module interfaces and source-library declarations are unchanged.

## Second reading by U1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
