# AlgebraicGeometry.ProEtale.CondensedRing.IdentityOpenModuleSections.identityOpenModuleSections

## Reason

Preflight conservatively classifies the added elaboration options and the irreducibility
attribute on a proved private helper as changes to commands visible to other modules.
These support elaborating the proof through the existing nested module-functor definitions.
The private comparison is marked irreducible so normalization rewrites do not unfold the
whole construction; its defining body is unfolded explicitly where needed.
No existing signature, predicate body, public import, or universe is changed.
The new import is private and exposes no additional API to importers.

## Old

```lean
set_option autoImplicit false

theorem identityOpenModuleSections :
    ProjectionGeometry.{u} ∧ OpenRestriction Λ ∧
      ∃ c : Comparisons Λ, UniqueNormalized Λ c ∧ Composition Λ c ∧ Identity Λ c
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

theorem identityOpenModuleSections :
    ProjectionGeometry.{u} ∧ OpenRestriction Λ ∧
      ∃ c : Comparisons Λ, UniqueNormalized Λ c ∧ Composition Λ c ∧ Identity Λ c
```

The added construction is `@[irreducible] private noncomputable def comparison`;
it composes the existing open-pasting comparison with identity pushforward. Its private
signature is used only in proved private helpers and the proof of the theorem above.
No private declaration occurs in an existing public signature or public definition.

## Users

`python3 tools/downstream.py Sheaf.AlgebraicGeometry.IdentityOpenModuleSections --uses
identityOpenModuleSections` reports zero downstream modules. The only textual declaration
use is in this item. No forced adaptation or target-statement review is required, as no
public definition or statement changes meaning. DAG parents are retained.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.IdentityOpenModuleSections | V9 | Proved original theorem; added private proof helpers and elaboration options. |

## Status

landed 20261023T152112-L-446348 2026-10-23 (merge of deliver/V9/Sheaf.AlgebraicGeometry.IdentityOpenModuleSections)
