## What changed

Restored `lean/Sheaf/Algebra/Homology/AffineTildeTensorSourceComparisonHelpers.lean`
from its exact `coord/rework.tsv` quarantine archive. Removed eight unused private
imports, selected the existing sheaf-module abelian instance with its universe
explicit, and stopped resetting the already globally irreducible `derivedPullback`.
All five helper proofs, both public signatures, all public imports, visibility,
and docstrings remain as archived. No source-library file is changed.

The module compiles cleanly in about five seconds. A separately compiled consumer
checks both original public signatures and their applications, plus the three
re-exported affine/pullback APIs. Both public helpers have only `propext`,
`Classical.choice`, and `Quot.sound` as axioms. The change record is
`coord/changes/T3-affine-tilde-source-helper-rework.md`.

## Proved and sorry left

Assigned rework repair; zero holes initially, zero closed, zero added, zero split
off, zero remaining. This is a compilation repair, not a new proof closure.

The existing complete proofs retained are `AlgebraicGeometry.leftCounit_naturality`
and `AlgebraicGeometry.leftDerived_comparison_on_resolution`, and the private
helpers `quotient_map_Qh`, `normalized_iso_of_resolution`, and
`normalized_unit_exchange`. No declaration contains `sorry`.

## No longer needed

Removed these private proof imports from this helper module:

- `Sheaf.Algebra.Homology.BaseDerivedTensorCohomologyModel`
- `WeilConjectures.Algebra.Homology.ExtensionKFlatQuasiIso`
- `Sheaf.AlgebraicGeometry.IsomorphismPullbackCounit`
- `WeilConjectures.AlgebraicGeometry.AffinePushforwardResolutionQuasiIso`
- `Sheaf.AlgebraicGeometry.Modules.IsKFlatTilde`
- `WeilConjectures.AlgebraicGeometry.TensorPullbackTilde`
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModel`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution`

The generic proofs use no declaration from those imports. No module or DAG node
is withdrawn; the parent affine source comparison still needs its own geometric
and tensor-model dependencies. Its proof plan and unit route are unchanged.

## Where the brief, the DAG or earlier work was wrong

This item is the explicitly listed zero-hole rework root, not a missing proof.
The original file is archived, not withdrawn. Its old private tensor-model import
collided with the adopted upstream model after the sync. Once that import was
removed, compilation exposed the outdated local abelian-instance expression and
the redundant local irreducibility setting, both repaired in this delivery.

There is no DAG node whose `lean.module` is this generic helper module; its
module docstring refers to `lem-pc-affine-tilde-tensor-source-comparison`, whose
attachment is the separate parent module. That attachment, statement, proof,
and dependencies remain intact. No node edit or new node is necessary.

The two direct consumer sources are still quarantined and have separate rework
entries. Their uses of these two public helpers were checked against the unchanged
signatures; the separate consumer check passes. They need no adaptation forced by
this repair. Search found the same generic helper proofs in the upstream twin;
importing that twin would also import incompatible copies of the retained affine
normalization modules. Retaining the archived helper proofs with their existing
public imports avoids that duplicate environment. Mathlib search found generic
left-derived uniqueness and projective-resolution naturality, neither requiring
a change to these already complete proofs.

## Second reading by T3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
