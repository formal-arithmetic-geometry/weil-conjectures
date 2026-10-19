# AlgebraicGeometry.ProEtale.coefficient_finite_descent_lisse proof commands

## Reason

The static interface comparison reports the extra open command, section variables and
local irreducibility attributes needed by the new private scalar coherence proofs.
Every pre-existing public signature, definition body and public import is unchanged.
The variables occur in closed helper sections; the attributes are explicitly local,
and the namespace opening is used while elaborating this file. They add no exported
instance, notation, global attribute or definition. The independent reader should
check these scopes and that the existing public API remains identical.

Two new public helper theorems are proved in their own modules and have new DAG nodes.
Their imports into the item module are ordinary proof imports.

## Old

The original opening and variables, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]
```

There were no local irreducibility commands in this module.

## New

The expanded opening and the first helper section, verbatim:

```lean
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace CategoryTheory
section
variable {C D : Type*} [Category C] [Category D]
  {F F' : C ⥤ D} {G G' : D ⥤ C}
```

Additional generic scalar section variables occur only in the sections `Scalar`
and `ScalarCoherence`, closed before the existing declarations. Their declarations
are private. The added attributes, verbatim:

```lean
attribute [local irreducible] Mod.extendScalars
attribute [local irreducible] retractNat Mod.extendRestrictAdjunction
attribute [local irreducible] lisseAlgClExtensionCompIso lisseFiniteExtensionCompIso
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.CoefficientFiniteDescentLisse | F1 | Closes its theorem from the two new proved helpers; public API unchanged. |
| Sheaf.Paper.CoefficientFiniteDescentObjects | unclaimed | Direct proof importer; statements and definitions unchanged. |
| Sheaf.Paper.CoefficientHeartClosure | unclaimed | Direct proof importer; statements and definitions unchanged. |
| Sheaf.Paper.FiniteCoefficientDescentTwoColimit | G7 | Direct public importer; uses the unchanged lisseFiniteExtensionCompIso in finiteDescentDerivedComp. |
| Sheaf.Paper.LisseFiniteCoefficientModel | new, F1 | New proved helper and node, no existing consumer. |
| Sheaf.Paper.LisseFiniteHomLift | new, F1 | New proved helper and node, no existing consumer. |

The required downstream scan found 302 transitive consumers. Its declaration-use
scan found only FiniteCoefficientDescentTwoColimit outside the item itself, using
lisseFiniteExtensionCompIso once. All transitive consumers retain the same existing
declarations. No target statement
or definition used by a target changes, so no target meaning review is reopened.
No consumer adaptation is necessary or included.

## Status

landed 20261019T002540-L-2151552 2026-10-19 (merge of deliver/F1/Sheaf.Paper.CoefficientFiniteDescentLisse)
