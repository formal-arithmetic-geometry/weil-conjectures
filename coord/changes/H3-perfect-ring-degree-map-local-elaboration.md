# CategoryTheory.perfectRingHom_tensorDual_degree_map_exists

## Reason

The complete signed evaluation proof needs local notation and conversion controls.
The static interface checker conservatively treats commands as interface changes.
All existing theorem signatures, definition bodies and public imports stay identical.
Only private helpers and proof imports are added. Local irreducibility keeps the
large chosen Hom and monoidal constructions folded; sequential elaboration avoids
competing conversion checks. These commands do not alter the imported API.

## Old

```lean
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
namespace CategoryTheory
```

No file-local irreducibility or sequential-elaboration command was present.

## New

```lean
set_option Elab.async false
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory TensorProduct
namespace CategoryTheory
attribute [local irreducible] homComplexFunctor SheafOfModules.monoidalCategory
```

The added namespace opening only resolves proof notation. Both attributes are local;
the elaboration setting does not change mathematical data or downstream options.
The existing theorem has its exact original signature and now has a complete proof.
No target statement or definition used by a target changes its meaning.

## Users

All seven transitive downstream modules reported by `tools/downstream.py` are listed.
Only PerfectRingHomTensorDegrees directly calls the theorem. No consumer needs an
adaptation because neither signatures nor public imports change. The original direct consumer
PerfectRingHomTensorDegrees compiled against the delivered module in 8.3 seconds.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.BaseChangeRHomPerfect | unclaimed | Same interface; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomKFlat | unclaimed | Same interface; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDegrees | unclaimed | Same theorem type; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDifferential | unclaimed | Same interface; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorDualIso | unclaimed | Same interface; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorPostcomposition | V1 | Same interface; no adaptation. |
| Sheaf.Algebra.Homology.PerfectRingHomTensorPrecomposition | unclaimed | Same interface; no adaptation. |

## Status

landed 20261020T132008-L-1400190 2026-10-20 (merge of deliver/H3/Sheaf.Algebra.Homology.PerfectRingHomTensorDegreeMap)
