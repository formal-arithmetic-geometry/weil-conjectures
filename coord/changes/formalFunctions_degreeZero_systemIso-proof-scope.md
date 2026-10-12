# formalFunctions_degreeZero_systemIso

## Reason

The static interface checker classifies additional commands as an interface change.
This delivery adds proof-elaboration transparency options, a noncomputable section
for private canonical comparison definitions, and a local registration of the already
existing `Scheme.Modules.enoughInjectives` instance. These commands affect elaboration
of this file. No existing public declaration, signature, or public import changes.
The scoped unused-variable linter option accommodates the unchanged existential
statement, whose predicate is `True` and deliberately does not mention its witness.

## Old

```lean
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
```

The existing signature is:

```lean
theorem formalFunctions_degreeZero_systemIso {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y, True
```

## New

```lean
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry
attribute [local instance] Scheme.Modules.enoughInjectives
```

Immediately before the theorem, `set_option linter.unusedVariables false in` scopes
the linter setting to that declaration. Its signature remains verbatim:

```lean
theorem formalFunctions_degreeZero_systemIso {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    ∃ b : formalFibreCohomologySystem f y (SheafOfModules.unit X.ringCatSheaf) 0 ≅
          formalFibreSectionsSystem f y, True
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroSystemIso
--uses formalFunctions_degreeZero_systemIso` found 222 downstream modules and only
these two textual users of the declaration. No interface change forces an adaptation.
No target statement or definition used by a target changes meaning.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroSystemIso | P3 | Own proof elaborates with local instances and transparency settings; identical public signature. |
| Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroDictionary | unclaimed | Its obtain of the system comparison still has exactly the same type; no edit required. |

All remaining downstream importers see the same existing public declaration and
public statement dependencies. They have no source references to the changed
proof-local commands; module-local options and local instance registration do not
export a new global instance.

## Status

landed 20261012T194130-L-461549 2026-10-12 (merge of deliver/P3/Sheaf.AlgebraicGeometry.FormalFunctionsDegreeZeroSystemIso)
