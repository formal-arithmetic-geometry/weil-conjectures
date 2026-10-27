## What changed

Proved source and target naturality of the two transpose functions in
AlgebraicGeometry.ProEtale.boundedSiteTensorTransposes_natural. The proof uses
the existing, proved boundedSiteTranspose_left and boundedSiteTranspose_right
calculations through a private import-all of BoundedSiteAdjunctionTranspose.
The etale identity uses the two naturality laws of the supplied adjunction.
All existing public signatures, definition bodies, docstrings and public imports
remain unchanged.

## Proved and sorry left

Closed one of the three original holes:
AlgebraicGeometry.ProEtale.boundedSiteTensorTransposes_natural.

Two original holes remain, both attached to
lem-pur-bounded-site-tensor-transposes:

- AlgebraicGeometry.ProEtale.boundedSiteTensorTransposes.
- AlgebraicGeometry.ProEtale.boundedSiteTensorTransposes_dualizing.

No holes added and no split-off statements. The completed naturality proof
introduces no new mathematical assumption.

## No longer needed

No import, module, node or dependency is withdrawn. The unfinished two
statements retain the existing DAG route and all its dependencies.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect was found. For the two remaining statements, the
canonical projection square and bounded Hom-chain compatibility suffice
categorically. The attempted complete proof did not pass the fixed compile
budget and is not included.

The expensive conversions occur between the monoidal instance implicit in
derivedTensor and independently inferred tensor/unitor instances. The
source library explicitly describes this issue in
WeilConjectures.SixFunctors.Etale.Derived.TensorStructure. A generic proof
of preservation of evaluation and the coefficient unit was constructed;
specializing it to the concrete comparison sheaf functor and combining
it with target naturality exceeded the per-file compilation budget.
Local irreducibility, explicit functor-level naturality, and sharing
nested class-instance proofs were tested. None yielded a verified full
module. No compilation limit was raised and no file was split in this
delivery.

## Second reading by V9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
