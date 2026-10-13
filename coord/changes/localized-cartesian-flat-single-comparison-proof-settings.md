# localized_cartesian_flat_single_comparison

## Reason

The static delivery checker classifies additional file-level elaboration commands
as an interface change. This record documents the proof-local settings explicitly.
No existing declaration signature, public definition body, or public import changes.
A new standard-localization helper is needed only by the proof.

## Old

```lean
universe u wX wS wW wY
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
```

## New

```lean
universe u w wX wS wW wY
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
attribute [local instance] Functor.additive_of_preserves_binary_products
```

The former additional local instance command for `isoTensorPullback_additive`
was removed in the repair. The proof now uses the existing public tensor-pullback
equivalence instance through a proof-only import of `IsoPullbackStalkCohomology`.

The private helper proofs use the following declaration-scoped settings:

```lean
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
```

The new universe is used only by private transport helpers. The open command
changes name resolution in this file; the instance attribute is local. The
settings affect elaboration of individual proofs. None changes the meaning of
any existing theorem statement, including targets that import this module.
The existing public theorem signature is byte-for-byte unchanged.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison
--uses localized_cartesian_flat_single_comparison` lists two actual declaration
users, including the defining module. The import graph has 1272 downstream modules,
all seeing the same public theorem type and public definitions. None needs adaptation.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison | U3 | unchanged public signature; proof filled using private helpers |
| Sheaf.AlgebraicGeometry.CartesianFlatSingleLocalizedBaseChange | unclaimed | unchanged application of the same theorem type; no adaptation |

There are no adapted existing modules in this delivery. The new module
`Sheaf.AlgebraicGeometry.StandardFlatSingleBaseChange` exports one named geometric
intermediate theorem with a documented sorry and its own new node.

## Status

landed 20261013T160713-L-1372447 2026-10-13 (merge of deliver/U3/Sheaf.AlgebraicGeometry.LocalizedCartesianFlatSingleComparison)
