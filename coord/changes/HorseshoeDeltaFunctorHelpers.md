# HorseshoeDeltaFunctor private proof helpers

## Reason

The stage-3 interface checker reports added `variable`, `open`, and `set_option`
commands as a possible interface change and requires this record. They support private
horseshoe data and proof helpers. No existing definition or theorem statement changes;
no public import changes, public instances, or public helper declarations are added.
The options affect elaboration in this file; the section variables introduce binders
only for the private helpers; the additional namespace opening resolves category laws.
The public theorem already specifies all its binders explicitly and keeps the same type.
No target statement or definition occurring in a target is altered.

## Old

```lean
open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory
```

The theorem follows immediately, with no section variables or helper declarations.

## New

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.Category

namespace CategoryTheory

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type u₁} {B : Type u₂} [Category.{v₁} A] [Abelian A]
  [EnoughInjectives A] [Category.{v₂} B] [Abelian B]
```

Private data and proved private helpers follow. `horseshoe_map_exact` omits the unused
section hypothesis `[EnoughInjectives A]`. Every new declaration is private, and the
existing theorem has its original signature and a complete proof.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor | U2 | Private helpers support the proof; the public theorem's type stays the same. |

`tools/downstream.py Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor --uses Horseshoe`
returns no users of the private helper data. The flagged change is to file-local
commands, not a public declaration. No importing module can name the private helpers,
and no downstream module needs adaptation. Public imports and public declarations
retain their names and signatures.

## Status

landed 20261012T035209-L-1575695 2026-10-12 (merge of deliver/U2/Sheaf.CategoryTheory.Abelian.HorseshoeDeltaFunctor)
