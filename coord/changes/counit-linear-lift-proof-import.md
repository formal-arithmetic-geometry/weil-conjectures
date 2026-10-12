# AlgebraicGeometry.etaleInverseImageModuleCounitLinearLift (proof import)

## Reason

The algebraic-structures theorem supplies finite-limit preservation only to the
proof. Its import must be private. Import the signature's definitions directly
through EtaleSheaves, Sites.Adjunction and the existing module pushforward import.
No declaration signature, definition or target meaning changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
```

## New

```lean
public import Sheaf.AlgebraicGeometry.EtaleSheaves
public import Mathlib.CategoryTheory.Sites.Adjunction
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import Sheaf.AlgebraicGeometry.EtaleInverseImageAlgebraicStructures
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleInverseImageModuleCounitLinearLift | E2 | Signature byte-for-byte unchanged; direct definition imports replace the proof-only public import. |
| Sheaf.AlgebraicGeometry.EtaleInverseImageModuleLinearCriterion | none recorded locally; last delivery M2 | No adaptation: already publicly imports EtaleInverseImageAlgebraicStructures and ModuleCat.Sheaf.PushforwardContinuous directly. The counit lift is only a proof import. Its statement and proof remain identical. |

The downstream scan found 178 transitive importers and two textual uses of the
declaration (the item and LinearCriterion), both listed above. LinearCriterion
is the sole direct importer and the sole downstream caller of the unchanged
counit declaration. All its downstream modules retain the same declarations and
imports through that module. No target statement or definition is altered and
no target meaning review is reopened.

## Status

landed 20261012T095858-L-315002 2026-10-12 (merge of deliver/E2/Sheaf.AlgebraicGeometry.EtaleInverseImageModuleCounitLinearLift)
