# SheafOfModules.geometric_module_construction: private proof support

## Reason

The delivery preflight reports changes to nondeclaration commands (`open`,
`variable`, and `attribute`) and requires this record. They support a completely
proved private implementation; they change no existing statement or definition.
The sole public declaration's signature is byte-for-byte identical to the
starting file. Its two public imports also remain identical. All additional
imports are proof-only. No target meaning changes and no caller adaptation is
required.

## Old

The original namespace/open/option block was:

```lean
open CategoryTheory CategoryTheory.Limits
namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
```

There was no `GeometricConstruction` namespace, variable block, or local instance
attribute. The theorem proof was `by sorry`.

## New

The namespace/open/option block is:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
namespace SheafOfModules

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

namespace GeometricConstruction

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
```

Every declaration inside `GeometricConstruction` is explicitly `private`.
The following attribute registers the private abbreviation `productExists` only
as a local instance within that namespace:

```lean
attribute [local instance] productExists
```

The namespace is closed before the original theorem. The private helper names
are opened for that theorem's proof:

```lean
end GeometricConstruction

open GeometricConstruction
```

The unused-variable style linter is disabled only for the original theorem, to
preserve its existing named nondependent forall binder `hRing` verbatim. No
proof-checking option is disabled. The complete new theorem proof constructs
both functors and verifies all the original equations.

## Users

`tools/downstream.py Sheaf.CategoryTheory.GeometricModuleConstruction --uses
geometric_module_construction` finds the following two modules mentioning the
declaration (the first is the declaration's own module). No declaration type or
public definition has changed, so all 417 modules in the import closure also
retain the same interface; none is edited or needs adaptation.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.GeometricModuleConstruction | A4 | Original signature preserved; sole hole proved; private helpers added. |
| Sheaf.CategoryTheory.GeometricModuleTransport | unclaimed in repository snapshot | Same theorem and hypotheses available; no change needed. |

## Status

landed 20261015T195757-L-1299441 2026-10-15 (merge of deliver/A4/Sheaf.CategoryTheory.GeometricModuleConstruction)
