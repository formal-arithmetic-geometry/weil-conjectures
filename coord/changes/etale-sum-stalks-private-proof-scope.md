# AlgebraicGeometry.Etale.exists_etaleSumStalksIso private proof support

## Reason

The theorem now has a complete proof, organized into private helpers in the namespace
`AlgebraicGeometry.Etale.SumStalks`. The static interface checker records the additional
namespace/variable/scoped-option commands, so this record documents their effect.
No existing signature, visibility, definition body, target, or public import changes.
No global instance or elaboration attribute is added. All new declarations, including
the local limits instance, are private.

## Old

Immediately inside the original namespace, the next command was the theorem's
classical scope:

```lean
namespace AlgebraicGeometry

open Classical in
```

There was no `Etale.SumStalks` helper scope or local limits instance. The existing
`Etale.exists_etaleSumStalksIso` signature is retained verbatim; its old proof was:

```lean
:= by
  sorry
```

## New

Before the unchanged theorem signature, the helper scope starts as follows:

```lean
namespace Etale.SumStalks

variable {U X : Scheme.{u}} (f : U ⟶ X) [Etale f]
  (A : Type (u + 1)) [CommRing A]
  {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (x : Spec (.of Ω) ⟶ X)

private local instance moduleLimits : HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} A) :=
  ModuleCat.hasLimitsOfSize.{u, u, u + 1, u + 1}
```

This supplies an already-proved Mathlib limits instance at the explicit universe
needed by the private skyscraper constructions. Its registration is local to this
namespace. Every helper is private. Each backward elaboration option uses `in` and
applies only to its individual private declaration. The helper namespace closes before
the original theorem; the original theorem's surrounding namespace and classical scope
are preserved. The new theorem proof constructs the equivalence from these private,
sorry-free helpers.

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.EtaleSumStalks --uses
AlgebraicGeometry.Etale.exists_etaleSumStalksIso` reports 389 modules transitively
downstream, and only the item itself textually mentions the theorem. There is one
direct importer, `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`, whose import
is proof-only. The following also records the four consumers named by the initial
static check of the formerly anonymous local instance. None sees a changed public
signature or active global instance, and none requires adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleSumStalks | S3 | Original theorem proved; private helpers added. |
| Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality | C3 | Direct proof importer; no statement or elaboration change. |
| Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility | X2 | Transitive importer; unchanged. |
| Sheaf.AlgebraicGeometry.OpenDirectImageFiniteCoefficients | X3 | Transitive importer; unchanged. |
| Sheaf.AlgebraicGeometry.SmoothTensorDuality | C2 | Transitive importer; unchanged. |

All other downstream modules are likewise unaffected: existing public signatures and
public imports are identical, and new helpers and instance registration are private/local.
No definition used by a target changes, so no target-meaning review is reopened.

## Status

landed 20261018T062908-L-674693 2026-10-18 (merge of deliver/S3/Sheaf.AlgebraicGeometry.EtaleSumStalks)
