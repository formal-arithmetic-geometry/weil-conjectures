## What changed

Completed all seven theorem proofs in `Sheaf.Paper.ConstantModelStratificationTransport`.
The stratification adapters are inverse by record eta and proof irrelevance. Fixed-cover
models transport by composing their model isomorphism with the pullback of the inverse
of the supplied isomorphism. Stratum and affine-open transport apply this construction
after further pullback. Constructibility retains the defining stratification and cover
witnesses in both branches of the qcqs/affine-local definition. Cohomology transports
constructibility and zero objects, then applies Mathlib's `DerivedCategory.isGE_iff` and
`DerivedCategory.isLE_iff` with the original bounds to obtain boundedness.

All declaration signatures, definitions and public imports are unchanged. The proof
follows the existing five-step node plan; no node update is needed. Compilation through
`lcompile.py` succeeded; delivery performs its independent compile and axiom checks.

## Proved and sorry left

Closed 7 of 7 holes, with no holes added or split off:

- `AlgebraicGeometry.Scheme.constructibleStratification_iff_locallyClosed`
- `AlgebraicGeometry.ProEtale.finiteConstantModelsOnCover_of_iso`
- `AlgebraicGeometry.ProEtale.finiteConstantPointModelsOnCover_of_iso`
- `AlgebraicGeometry.ProEtale.stratifiedConstantModels_of_iso`
- `AlgebraicGeometry.ProEtale.affineStratifiedConstantModels_of_iso`
- `AlgebraicGeometry.ProEtale.constantModelConstructible_transport`
- `AlgebraicGeometry.ProEtale.constantModelCohomology_transport`

All realize `lem-sf-constant-model-stratification-transport`. No `sorry` remains in the
item, and the packet adds no other modules.

## No longer needed

Removed the unused private proof import
`Sheaf.CategoryTheory.RightDerivedFunctorOfQuasiIsoResolutions`. Neither arbitrary
K-injective resolutions nor construction of a right derived functor is used by any
transport assertion. This does not assert that the module is unused by other consumers.
All five declared proof dependencies of the item's node remain used through their
record, pullback, local-model and constructibility interfaces; no DAG dependency or
unit-route step is pruned.

Searches through `msearch.py` used Lean Finder for local-model/cohomology transport,
Loogle for `IsZero.of_iso`, and grep for the local-model and constructibility names.
Source search found the same local isomorphism argument inside
`constantModelConstructibleFiniteTor_wellDefined`; the direct construction here also
retains the specified covers and scalar modules required by the finer statements.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. The private right-derived-functor import was
unnecessary. The affine witness theorem does not need its affine-open proof for the
transport itself: the stronger functorial restriction argument works for any open.
The assumption remains in its unchanged statement; unpacking `hU` retains its
role in the proof term and avoids the unused-variable warning.

The record arguments also cover empty stratifications and empty covering index sets.
No ordering assumption on the cohomological endpoints is needed: even when the interval
is empty, the supplied vanishing gives both t-structure bounds directly. The non-qcqs
branch retains separate witnesses on each affine open rather than asserting a global
finite stratification. The latest blueprint's constructibility paragraph and the unit
record were checked; the unit's route is unchanged.

## Second reading by C5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
