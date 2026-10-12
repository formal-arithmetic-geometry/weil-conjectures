# AlgebraicGeometry.Scheme.Modules.quasicoherent_finite_type_affine

## Reason

The stage-3 static interface scanner compares all nondeclaration commands. It therefore
requests a change record for the extra `open`, `section`, `universe`, and `variable` commands
used to state the proved private helpers. They only control elaboration of this file. The
public theorem's original binders, universes, statement, attributes and visibility remain
identical. Public imports remain identical, and the added import is proof-only.
No definition or target statement changes, so no target statement review is reopened.

## Old

The old module-level elaboration commands before the theorem were:

```lean
universe u v

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules
```

The theorem's original complete signature is preserved in the delivered module and in its
node's unchanged `lean.statement` field.

## New

The initial commands are now:

```lean
universe u v

open CategoryTheory CategoryTheory.Limits TopologicalSpace

section SiteHelpers

universe u₁ u₂ v₁ v₂

open SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
```

This section contains only private proved helpers, with additional variables for the target
site and a nested `Locality` section; both sections close before the scheme namespace.
Within the scheme namespace the private proved helpers use:

```lean
variable {X Y : Scheme.{u}}
```

The main public theorem still binds `X : Scheme.{u}` explicitly, shadows that helper variable,
and retains exactly its original statement and universe-polymorphic affine-cover clause.
The delivered source contains every command and its scope; no command registers a global
instance or changes an existing definition. There are no forced adaptations.

## Users

`tools/downstream.py ... --uses quasicoherent_finite_type_affine` reports the following
modules mentioning the existing declaration. The transitive import closure has 479 modules;
only two downstream modules mention this theorem. All statements and meanings stay identical.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine | W3 | Proof and private helpers changed; signature identical. |
| Sheaf.AlgebraicGeometry.CoherentAlgebraAffineFiniteProper | unclaimed | No adaptation: existing theorem signature and public imports identical. |
| Sheaf.AlgebraicGeometry.FinitePushforwardCoherent | unclaimed | No adaptation: existing theorem signature and public imports identical. |

The other transitive importers also retain the same visible declarations and public imports;
the new helper declarations are private and the additional import is proof-only.

## Status

landed 20261012T150959-L-2232925 2026-10-12 (merge of deliver/W3/Sheaf.AlgebraicGeometry.QuasicoherentFiniteTypeAffine)
