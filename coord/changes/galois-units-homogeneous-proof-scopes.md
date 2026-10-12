# Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent proof command scopes

## Reason

The stage-3 preflight conservatively reports any changed non-declaration command as an interface change, including proof-local `open`, `section`, `variable`, and elaborator options. This record documents those commands. No existing declaration signature, visibility, public import, or definition changes. All new declarations are private helpers used solely in proofs. The `backward.isDefEq.respectTransparency` option controls elaboration of categorical cochain coercions, not any mathematical data or theorem statement.

The initial module-scoped local discrete-topology instance was moved into `action_continuous`; the delivered module adds no instance at module scope. The two original public theorems and the public cocycle abbreviation keep their exact signatures.

## Old

The original context commands were:

```lean
@[expose] public section
universe u
namespace Field
```

followed by the three existing public declarations, ending with `end Field`.

## New

The delivered proof context begins:

```lean
@[expose] public section

universe u r v

namespace Field
open CategoryTheory TopRep
noncomputable section
set_option backward.isDefEq.respectTransparency false

section Cochains

variable {R : Type r} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [LocallyCompactSpace G] (A : TopRep.{v} R G)
```

`end Cochains` closes the generic helper variables before the original public declarations. The field-specific private helpers use `variable (K : Type u) [Field K]`; each original declaration continues to bind its own `K` explicitly. A final unnamed `end` closes the noncomputable section before `end Field`. The private helpers now explicitly put the group and coefficient carrier in the same universe `v`, which includes the Galois application. Their aliases have type `TopModuleCat.{v} R`. This prevents repeated universe inference from expanding nested coinduced representations. The added universes `r` and `v` do not occur in any original public declaration.

These commands introduce no public declarations or instances and do not alter any existing elaborated type. There is no definition or statement correction.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent | S1 | Both existing proofs completed; signatures and public imports identical. |
| Sheaf.FieldTheory.GaloisUnitsHomogeneousComparison | unclaimed | Only direct importer; both applications remain unchanged and no adaptation is needed. |

`tools/downstream.py` found this direct importer as the only external user of the cocycle-equivalence declaration; the descent declaration is also used there. The remaining downstream closure uses that importer. No user has a changed statement or definition because these are local proof commands and private helpers. No dependent module is adapted, and no target statement or target definition changes.

## Status

landed 20261012T160830-L-2612354 2026-10-12 (merge of deliver/S1/Sheaf.FieldTheory.GaloisUnitsHomogeneousCocycleDescent)
