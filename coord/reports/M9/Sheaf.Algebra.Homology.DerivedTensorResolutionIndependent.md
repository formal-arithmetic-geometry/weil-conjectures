## What changed

Proved `AlgebraicGeometry.Scheme.derivedTensor_resolution_independent` with its full
original signature, including tensor quasi-isomorphism, existence, agreement,
identity, cocycle and uniqueness. The three existing tensor definitions are unchanged.
All new helper theorems are private and proved in the item module.

The shorter route resolves the second factor once as `r : R → K₂`. Each resolution
`q : P → K₁` has the common localized model `Q(K₁ ⊗ R)`, via the two tensor maps
out of `P ⊗ R`. Their zigzags define the comparison. Tensor homotopy invariance
proves agreement; cancellation proves identity and cocycle. A common K-flat roof,
constructed with the right Ore axiom, proves uniqueness. No direct lift is assumed.

Added proof imports for tensor preadditivity, double-complex flip and tensor
homotopies. Updated the existing node's proof, proof dependencies and proof origin.
The unit has no realized statement or proof-step nodes here, so its route is preserved.
There are no definition or statement changes, consumer adaptations or new modules.
The required change record is `coord/changes/derived-tensor-resolution-independent.md`.

The similarly named tensor helpers in `SiteDerivedTensorDescent` and
`ProEtaleResidueTorTest` are private (in different namespaces) and cannot be imported.
The former also fixes the site and coefficient universes together. The local proved
helpers specialize the public tensor/cone and double-complex APIs to the independent
coefficient universe required by the unchanged statement.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.derivedTensor_resolution_independent`
(node `lem-weil-derived-tensor-resolution-independent`).

Added 0 holes; split off 0 obligations; no `sorry` remains in the delivery.
The retained attempt's unfinished comparison helper is removed: its argument is
proved directly inside the original theorem. This is a proof, not a decomposition.
The resumed `lcompile.py` check compiled in 30.4 seconds with exit code 0 and no warnings.
The delivery preflight also checks axioms.

## No longer needed

Removed proof imports:

- `Sheaf.Algebra.Homology.KFlatClosure`
- `Sheaf.Algebra.Homology.AcyclicKFlatTensor`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

Removed planned proof dependencies:

- `lem-pc-kflat-cone-direct-sum`: no need to prove the comparison cone K-flat.
- `lem-pur-acyclic-kflat-tensor-arbitrary`: each tensor argument instead uses an acyclic
  cone against a factor already known K-flat, directly from the definition.
- `lem-pc-right-fraction-representation`: no arbitrary derived-arrow functor is built;
  the Ore axiom alone constructs the roof needed for uniqueness.
- `lem-pc-right-fraction-common-refinement`: no equality criterion for arbitrary roofs
  is needed; agreement and cocycle on one common K-flat roof give uniqueness.

The associated KFlatClosure and AcyclicKFlatTensor modules are not needed by this
proof. Other importers may still need them. The source finite-coefficient tensor
functor is unused here: the unchanged statement uses `Scheme.derivedTensor` from
`Sheaf.Algebra.Homology.DerivedTensor`, whose concrete chosen-resolution model is
used directly. All original public imports are retained.

## Where the brief, the DAG or earlier work was wrong

The original cone-closure and arbitrary-roof functor construction is longer than
necessary: resolving the second factor supplies one common tensor model for the
entire comparison family. The original mathematical statement needs no correction.
The retained sandbox had no report or node update and had an unfinished public
comparison helper; that helper has been replaced by the complete argument.

The retained dry-run diagnostic requested a change record for the new local
notation and declaration-scoped elaboration options. The supplied record lists
the commands and all five downstream importers; no consumer needs adaptation.
No second reader is claimed in this report.

## Second reading by M9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
