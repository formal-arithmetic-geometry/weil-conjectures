## What changed

Proved `AlgebraicGeometry.Scheme.finiteStageDerivedExtensionByZero_constructibleFiniteTor`
in `Sheaf.Paper.OpenExtensionFiniteTor`, retaining its signature and the definition of
`finiteStageDerivedExtensionByZero` verbatim. All new imports are proof-only.
The two private proved helpers transfer constructibility through canonical scalar realization,
then use the existing etale origin, extension-by-zero constructibility and comparison isomorphism.
Exactness transports homology and its finite support. For Tor amplitude, extend a bounded flat
model termwise and apply the existing flat-model characterization in reverse. Flatness is
preserved by `openClosedFlatness_proEtale`; residue invertibility follows from the finite-field
cardinality and the supplied distinct-prime hypothesis. Cohomological and Tor intervals remain
independent. Updated the existing DAG node to describe this route.

Validation: the completed module compiled through `lcompile.py` in 5.1 seconds. The first server
request received no answer, and the prescribed retry compiled successfully. The code covers
empty schemes, the zero complex, zero coefficients, and any ordered Tor interval: the existing
comparison and flat-model results include those cases, and the zero terms are transported
by additivity. No consumer adaptation is needed because signatures, definitions and public
imports are unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.finiteStageDerivedExtensionByZero_constructibleFiniteTor`
(blueprint `lem-trf-open-ctf`). Added 0 holes and split off 0 statements. No `sorry` remains
in the delivered module. Both private helper theorems are proved.

## No longer needed

Removed these proof-only imports:

- `Mathlib.Topology.Constructible`
- `Mathlib.Topology.LocallyClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleRingedOpenClosed`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedPullbackComposition`
- `Sheaf.AlgebraicGeometry.ProEtaleOperations`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenTensor`
- `Sheaf.Paper.DerivedPullbackTensorHom`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.IntegralFinitePullbackComposition`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.SfCommonStageWeilCohomology`

The direct dependency on `lem-trf-open-tensor` is replaced by `lem-sf-flat-model` and
`lem-sfb-open-closed-flatness`. The direct dependencies on
`lem-weil-pbc-proetale-ringed-open-closed` and
`lem-weil-pbc-proetale-derived-pullback-composition` are replaced by the existing etale
constructibility and extension comparison results; their obsolete top-level tool approvals
were removed. The topology-only imports and their nodes `def-weil-constructible-subset` and
`def-weil-locally-closed-subset` are not directly needed: the existing constructible extension
lemma already performs the stratification argument. The proof needs neither the common-stage
cohomology construction nor integral pullback composition, ordinary-etale finite-Tor categories,
or the general multi-stage operations of `def-weil-derived-pullback-tensor-hom`.
These are direct pruning claims only; some modules remain reached through other library imports.
The coefficient, finite-type, constructibility and finite-Tor definitions remain in use.

## Where the brief, the DAG or earlier work was wrong

The original node route is mathematically sound. Existing library results make its glue shorter:
etale constructible origin plus extension comparison supplies the stratification argument, and
bounded flat models give the Tor interval without a new derived tensor comparison.
The unit record has no separately realized steps, so no unit statement or realized proof step
is bypassed. The original proof-plan docstring remains as its source argument; the DAG records
the implementation actually checked by Lean.

The flat-model characterization and open-closed flatness are reused as generic tools. The
constructibility encoding, realization restriction, fixed-module origin, etale extension
constructibility and extension comparison are likewise existing results; no new nodes are needed.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
