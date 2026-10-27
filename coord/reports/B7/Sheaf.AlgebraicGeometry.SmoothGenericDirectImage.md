## What changed

Proved the assembly of
`AlgebraicGeometry.Etale.exists_nonempty_open_smooth_directImage_lisse_baseChange`
from a compact dual model, without changing its statement or public imports.
The private generic-constancy argument intersects the dense lisse opens for the finitely
many relevant homology sheaves. Exact inverse image transports the homology bounds and
local systems to this common open. Field duality reverses the bounds to `[-b,-a]`.
The equality in the model, followed by cancellation of the target isomorphism, proves
invertibility of the specified ordinary exchange.

Added `Sheaf.AlgebraicGeometry.SmoothCompactDualModel`, including an explicit data record
with named complex, isomorphism and exchange projections. This separates the relative compact
dual construction and its canonical pairing compatibility from generic constancy.
The new result has no generic-open or lisse-direct-image conclusion; it supplies a
bounded constructible global model and a comparison equality for every open and test square.
No object is defined by choosing a witness from this admitted existence theorem.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Etale.exists_nonempty_open_smooth_directImage_lisse_baseChange`
(node `lem-asd-smooth-generic-direct-image`). The item module has zero remaining holes.
Added one hole in
`AlgebraicGeometry.Etale.exists_smooth_compact_dual_model`
(node `lem-asd-smooth-compact-dual-model`). Its source and full proof in words are in
its docstring and node. This is one closed hole and one added hole: a decomposition,
with net zero holes closed, not a completed geometric proof of the whole dependency chain.
The generic shrinking, reversed bounds, local constancy and exchange cancellation contain
no further admissions. Both modules compiled without warnings through the project compile service
(model 29.5 seconds; item 26.3 seconds). Local transparency settings and irreducibility attributes keep
derived-functor implementations behind their API without changing any public definition.

## No longer needed

Removed the following direct proof imports from the item:

- `Mathlib.AlgebraicGeometry.Noetherian`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `Sheaf.AlgebraicGeometry.CompactBoundedConstructibleBaseChange`
- `Sheaf.AlgebraicGeometry.CompactProjectionExchange`
- `Sheaf.AlgebraicGeometry.CompactSupportFiniteTorsion`
- `Sheaf.AlgebraicGeometry.FiniteLisseFieldDual`
- `Sheaf.AlgebraicGeometry.SmoothExceptionalBaseChange`
- `Sheaf.AlgebraicGeometry.SmoothTensorDuality`
- `Sheaf.SmoothPurity.InternalAdjunctionEvaluation`
- `WeilConjectures.Algebra.Homology.DerivedInternalHom`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `WeilConjectures.Compactification.BaseChange`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.TensorHom`

The geometric nodes behind these imports remain needed by the compact-dual-model node.
They are moved below that node, not withdrawn. No library module or source declaration
is deleted or claimed globally pruned. The original unit has no realized statement or
steps to bypass (`dag/units/sk-prop-sf-cbc.json`).

## Where the brief, the DAG or earlier work was wrong

The finite-ring source theorem `AlgebraicGeometry.Etale.smoothGenericDirectImage` is
admitted and its node `lem-fin-smooth-generic-direct-image-finite-ring` depends on this
item. Using it as a shortcut would make a circular DAG argument, so it is not imported.
The model comparison uses compact exchange on D-plus: ordinary right derived direct
image is bounded below, and tensoring its pullback with bounded locally finite-free N
stays bounded below. It does not assume the ordinary direct image is already bounded
constructible.

The original DAG treats the relative dual construction and the full exchange pairing
comparison as steps, but no single existing declaration has their combined interface.
The new model records that separate obligation rather than assuming that an abstract
object isomorphism identifies the actual exchange map.

## New nodes

`lem-asd-smooth-compact-dual-model` in `dag/nodes/sec-smooth-purity/` records
`AlgebraicGeometry.Etale.exists_smooth_compact_dual_model`, in the new module
`Sheaf.AlgebraicGeometry.SmoothCompactDualModel`. It isolates the relative compact dual
and pairing comparison from the subsequent generic-lisse argument. Its proof dependencies
retain the geometric steps of the original node. Edge cases: the empty source has the
zero model; zero local systems have zero model; varying dimensions use the finite clopen
decomposition; empty opens have the zero sheaf categories. Arbitrary Noetherian test
schemes remain allowed and the canonical dual-pullback map is explicitly named.

`def-asd-smooth-compact-dual-model` records the `SmoothCompactDualModel` structure in
the same module. Its fields package the complex and comparison data; the definition makes
no choice and invokes no unproved theorem. The structure API prevents repeated expansion
of the large nested existential comparison type during kernel checking.

Change record: `coord/changes/B7-smooth-generic-direct-image-local-elaboration.md`
documents the local elaboration commands flagged by the interface detector and the new
record API. No existing downstream module needs adaptation.

## Second reading by B7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
