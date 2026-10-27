## What changed

The original statement of `scalar_tensor_pull_normalization` is unchanged. Its proof
forms the scalar and tensor routes as natural transformations, computes both routes
in a common ordinary homotopy tensor model, cancels the model target on representatives
whose ordinary pullback is K-flat, and descends along an isomorphism to each arbitrary
derived object by naturality.

`InternalScalarTensorPullModels` constructs the exact restriction/pullback and
regular-coefficient comparisons, the model target and its common model map. These
are actual composites; no definition contains a hole or chooses an unspecified witness.
`InternalScalarPullRouteModel` and `InternalCanonicalTensorPullRouteModel` isolate the two
independent computation steps. `InternalTensorPullRouteModel` proves that an arbitrary
normalized tensor presentation has the canonical derived hom component: compare on a
K-flat representative, cancel the one-factor localization tensor map, then descend by
naturality. It uses this uniqueness to prove the general tensor-route assertion from
the canonical one. The scalar computation uses only the X normalization
and the scalar pullback normalization; the tensor computation uses only the Y
normalization and the canonical geometric tensor comparison. Neither is the original
square under another name.

All existing public imports and signatures are preserved. New proof imports are private.
The existing native tensor-model and flat-preservation APIs replace the proposed
transport through section-module categories.

Validation: all five current modules compile through `lcompile.py` with no warnings.
The final tensor-route and item-module run completed in 19.1 s and 42.0 s respectively;
the three unchanged supporting modules had already compiled in import order.
The original theorem signature and public import list were compared byte for byte
with the shared source and are unchanged. Every new DAG dependency list is the union
of its proof steps' `uses`, and all Lean lines are within 100 characters.

## Proved and sorry left

Original holes: 1, in
`AlgebraicGeometry.ProEtale.QuotientChange.scalar_tensor_pull_normalization`.
Its body is now a complete proof from the two route computations. The model target's
invertibility and the passage from resolving representatives to arbitrary derived
objects are proved in this delivery.

Added holes: 2, each the entire body of a named public theorem:

- `AlgebraicGeometry.ProEtale.QuotientChange.scalar_pull_route_model`
  (`lem-sfb-internal-scalar-pull-route-model`).
- `AlgebraicGeometry.ProEtale.QuotientChange.canonical_tensor_pull_route_model`
  (`lem-sfb-internal-canonical-tensor-pull-route-model`).

`AlgebraicGeometry.ProEtale.QuotientChange.tensor_pull_route_model` is proved using
the normalization uniqueness and the canonical route lemma.

The item module has zero holes; the delivery has two. This is a decomposition, not
a net proof closure: one upper hole is replaced by two strictly smaller computation
obligations. It gives no positive sorry-ledger progress claim.

## No longer needed

No existing public import is removed and no existing module is withdrawn.
The new tensor-route proof uses the general one-factor derivability API directly,
so its draft import of
`WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Dualizable` was removed;
the duality declarations are not needed. The original
planned proof dependencies below are not used by the assembly proof, or by the stated
proof plans for its two model computations:

- `lem-pc-kflat-resolution` / `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`:
  the existing internal-module `residue_exists_kFlatMap_iso` API supplies the needed representatives.
- `lem-weil-pbc-ringed-pullback-preserves-kflat` / `Sheaf.Paper.KFlatRingedToposPullback`:
  representatives with K-flat ordinary pullback are chosen directly.
- `lem-pur-kflat-tensor-quasiiso-independent` /
  `Sheaf.Algebra.Homology.KFlatTensorPreservesQuasiIsoIndependentCoefficients`:
  `Functor.tensorModelTarget_isIso` gives exactly the one-factor comparison to cancel.
- `lem-sfb-internal-scalar-pullback-normalization` /
  `Sheaf.Paper.InternalScalarPullbackNormalization`: the supplied normalization hypotheses
  suffice; their existence theorem is not needed.
- `lem-pe-internal-section-tensor-comparison` /
  `Sheaf.CategoryTheory.InternalSectionTensorComparison`: work stays in internal modules.
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback` /
  `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`: the statement already specifies
  the native geometric tensor comparison and its native counit API is used instead.

`new-integral-residue-ordinary-tensor-normalization` remains needed by the scalar
route computation. `def-sfb-module-object-projection-map` remains available through
the original public import and supplies the native tensor comparison interface.
These dependency changes do not claim global unreachability of any module.

## Where the brief, the DAG or earlier work was wrong

The old plan proposed transport through section-module K-flat models. The internal
library already has a common homotopy tensor model, its one-factor invertibility
lemma and representatives with K-flat ordinary pullback, so that transport is
unnecessary for the assembly. The separate residue square does not prove this item
as written: it is specialized to integral residue coefficients and chosen comparison
maps, whereas this item allows arbitrary condensed coefficient maps and any
comparisons satisfying the specified normalizations.

Edge-case review covered the identity coefficient map, zero coefficients, zero complexes
and empty schemes. Each uses counit identities without cancelling a
noninvertible tensor comparison, so the nonflat and unbounded cases are retained.
The unit's statements and proof route are unchanged. No source-library declaration,
existing definition or existing theorem signature was changed, and no change record
is needed.

## New nodes

`def-sfb-internal-scalar-tensor-pull-models` records the constructed comparison maps
and the common model.

`lem-sfb-internal-scalar-pull-route-model` records the scalar counit and ordinary
balancing computation.

`lem-sfb-internal-tensor-pull-route-model` records the proved reduction to the
canonical tensor presentation.

`lem-sfb-internal-canonical-tensor-pull-route-model` records the remaining canonical
tensor counit computation.

Each inherits the item's chapter and unit, records the source of the corresponding
original proof step, and has a Lean attachment. The original node now records the
actual cancellation and naturality descent argument. No change records are needed.

## Second reading by W2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
