# Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories import interface

## Reason

The mathematical definitions and all existing theorem signatures are unchanged.
The proof uses the source library's already-proved generic cohomology criterion,
so the public wrapper import is replaced by the source interface it re-exported.
The latter remains public because `DerivedCategory.homologyProperty` occurs in
this module's public definitions. Stalk arguments also need proof-only imports
and the local `Limits` and `ZeroObject` namespace openings. Fully proved private
instances provide subobject, quotient, zero and extension closure; they do not
add public declarations. The static import-pruning check reports no missing
imports or declarations downstream.

## Old

```lean
public import Sheaf.Paper.CohomologyInWeakSerreSubcategory

open CategoryTheory
```

## New

```lean
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Mathlib.Algebra.Homology.ShortComplex.Ab

open CategoryTheory Limits ZeroObject
```

All existing definitions and theorem signatures are literally unchanged.
The other original imports remain. The only lost public declaration is the
unused statement-only wrapper `CategoryTheory.cohomology_in_weak_serre_subcategory`.
Its generic conclusion is supplied by the already-proved source instances;
no downstream source mentions the wrapper theorem. No target meaning changes.

## Users

All transitive users reported by `tools/downstream.py` are listed below, with
holders as recorded in this machine's coordination snapshot. No downstream
module is adapted by this delivery.

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.BoundedAllowableTorsionSmoothBaseChange | B2 | Existing signatures and definitions unchanged; no use of the removed wrapper theorem. No adaptation needed. |
| Sheaf.AlgebraicGeometry.BoundedBelowDerivedSmoothBaseChange | A4 | Existing signatures and definitions unchanged; no use of the removed wrapper theorem. No adaptation needed. |
| Sheaf.AlgebraicGeometry.BoundedBelowTruncationCriterion | A4 | Existing signatures and definitions unchanged; no use of the removed wrapper theorem. No adaptation needed. |
| Sheaf.Targets.EtaleSmooth | C1 | Existing signatures and definitions unchanged; no use of the removed wrapper theorem. No adaptation needed. |
| Sheaf.Targets.EtaleSmoothRing | A2 | Existing signatures and definitions unchanged; no use of the removed wrapper theorem. No adaptation needed. |
| TargetsCheck | unclaimed | Existing signatures and definitions unchanged; no use of the removed wrapper theorem. No adaptation needed. |

## Status

landed 20261015T154148-L-157809 2026-10-15 (merge of deliver/A4/Sheaf.AlgebraicGeometry.AllowableTorsionDerivedCategories)
