## What changed

Preserved the statement of `WeilConjectures.PurityFiniteSetting.tower_geometric_purity_mate`
and its conclusion definition. Its proof constructs the geometric-fiber hypotheses,
uses `schemeGeometricFrobenius_squares`, transports along the compactification equation,
and specializes the new proved `SpGeometricPurity.isomorphism_purity_result`.

The assembly combines two separate orientation/tensor identities using tensor naturality
and composition of product morphisms. It cancels the purity isomorphism to get conjugation,
reflects component invertibility through realization to obtain an invertible mate,
derives source naturality by conjugating natural transformations, expands the exact
adjunction transpose, and composes normalization preservation in both orders.

Moved the eleven existing public data declarations, verbatim, into
`TowerGeometricPurityData` and publicly re-exported them. This permits the three remaining
lower geometric statements to be separate modules without an import cycle. No existing
consumer or adopted-source module was edited. See change record
`coord/changes/P4-tower-geometric-purity-data-relocation.md`.

## Proved and sorry left

Original holes: 1. Closed in the item:
`WeilConjectures.PurityFiniteSetting.tower_geometric_purity_mate`.
The item now has 0 holes. Also proved the new
`AlgebraicGeometry.ProEtale.SpGeometricPurity.isomorphism_purity_result`, with complete
private tensor-factor and mate-component proofs. Also proved
`AlgebraicGeometry.ProEtale.SpGeometricPurity.purity_presentation_retagging`: the orientation
comparison is an actual application of the existing orientation-retagging theorem, and only
the tensor-model comparison remains below it. The data module has 0 holes.

Validation: the final assembly and item compiled cleanly through `lcompile.py`
in 30.7 seconds and 49.3 seconds respectively. The lower presentation lemma and
all statement/data modules also compiled; delivery repeats the complete packet check.
The declaration parser confirms all thirteen original signatures and all twelve
non-theorem bodies are unchanged, including the eleven relocated interfaces.

Added 3 lower holes, each in its own module with source, complete proof in words and node:

- `AlgebraicGeometry.ProEtale.SpGeometricPurity.isomorphism_tower_pullback`
  (`lem-pur-isomorphism-tower-pullback`): domain/normalization preservation and strict roots.
- `AlgebraicGeometry.ProEtale.SpGeometricPurity.tensor_presentation_retagging`
  (`lem-pur-tower-tensor-presentation-retagging`): the projection-counit and tensor-transpose
  comparison for arbitrary normalized tensor presentations. The orientation clause is proved.
- `AlgebraicGeometry.ProEtale.SpGeometricPurity.semilinear_purity_factors`
  (`lem-pur-tower-semilinear-purity-factors`): exchange invertibility and the separate
  orientation and tensor-transpose equations.

This is a decomposition of one upper hole into three strictly lower holes, not a net
closure reduction. None asserts the original Result under another name: the genuine
Lean assembly proves its purity square, conjugation, source naturality, mate invertibility,
transpose and normalized-composite fields from the lower statements.

## No longer needed

Removed the original module's private proof imports
`Sheaf.Paper.TowerTensorTransposeGroundFieldRetagging`,
`Sheaf.Paper.OrientationGroundFieldRetagging` and
`Sheaf.SixFunctors.ProEtaleIsomorphismInverseImage`. Their needed geometric arguments
are represented in the lower statements and their DAG proof dependencies.
`OrientationGroundFieldRetagging` is used directly by the proved presentation lemma.
Removed the unused private proof imports from the three holed modules as well:
`IsoSectionwiseInverseImage`, `SmoothPurityBaseChangeFactors`,
`TowerTensorTransposeGroundFieldRetagging` and `CochainTensorModelRigidity`.
Their declared lemmas remain the source plan of those lower nodes; they will be
imported when those proofs are written. The holed modules need only the public data
interfaces to state their genuine geometric steps.

No global node or module is claimed pruned: the original geometric dependencies remain
needed in the lower arguments. No unit statement or realized proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The planned tensor-retagging theorem supplies existential normalized tensor models,
whereas the requested Retagging field quantifies over arbitrary existing `Purity` data.
It cannot be applied directly to the two recorded `tensorX`/`tensorY` fields. The new
presentation-comparison step explicitly records the missing constraint-independence
argument, justified by signed cochain representatives and tensor-model rigidity.

The k-linear tower preservation statements do not directly cover the semilinear
geometric-Frobenius self-maps. The isomorphism inverse-image step states their exact
ordinary-tower domain and normalization consequence. The two-factor step records the
retagging and adjoint-comparison glue needed to use the existing k-linear base-change
factors with the specified compactification and counit mate. No false statement or
changed target is asserted. Edge cases checked in the proof descriptions: dimension
zero, empty schemes, positive quotient index, nonnormalized ctf inputs, arbitrary
normalized tensor models and arbitrary same-support right adjoints.

## New nodes

`def-pur-tower-geometric-purity-data` attaches the unchanged eleven explicit interfaces
to their extracted data module. It adds no mathematical assumption or hole.

`lem-pur-isomorphism-tower-pullback` is the exact site-equivalence, flat-resolution and
strict-root step of the original proof, independently usable for any scheme isomorphism.

`lem-pur-tower-purity-presentation-retagging` proves the orientation comparison by
specializing the existing theorem and combines it with the narrower tensor comparison.

`lem-pur-tower-tensor-presentation-retagging` isolates only the actual projection-counit
and tensor-transpose comparison; tensor-model rigidity fixes the gap between existential
model data and the supplied arbitrary models.

`lem-pur-tower-semilinear-purity-factors` isolates the two constituent base-change
equations after retagging and counit-preserving adjoint transport. It does not contain
the purity square or the other Result clauses.

`lem-pur-isomorphism-purity-assembly` is proved and combines these steps by explicit
categorical calculations. The original node now records the actual Frobenius
specialization route. Change record:
`coord/changes/P4-tower-geometric-purity-data-relocation.md`.

## Second reading by P4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
