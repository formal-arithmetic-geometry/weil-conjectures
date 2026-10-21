# Completed coefficient resolution proof instances

## Reason

The proof works with independent scheme and coefficient universes. Its tensor
calculation needs the existing coefficient-sized sheafification, size, and
filtered-colimit witnesses without selecting a smaller coefficient universe.
The static interface check lists the new anonymous local instances, so this
record documents their scope and the effect on the sole downstream module.

## Old

There are no corresponding local instance declarations in the original module.
The existing public definitions and theorem signature remain verbatim.
The existing exclusion of
`CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall` is retained.

## New

The following declarations are all inside `section ReductionTensorInstances`:

```lean
local instance (priority := high + 1) :
    HasSheafify (AlgebraicGeometry.Scheme.ProEt.topology T)
      AddCommGrpCat.{max u (t + 1)} := integralCoefficientAbSheafify T

local instance : EssentiallySmall.{max u (t + 1)} T.ProEt := essentiallySmallSelf.{u} _
local instance : PreservesFilteredColimitsOfSize.{t + 1, t + 1}
    (CategoryTheory.forget AddCommGrpCat.{max u (t + 1)}) :=
  preservesFilteredColimitsOfSize_shrink _
```

Their instance registrations end with that section, before the remaining
resolution, completeness, and derived-triangle proofs. Each witness is an
existing library construction. The public data and theorem statements are
unchanged; no global instance registration is added by these declarations.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SupportedLatticeHomReductionTower | unclaimed | Imports the item privately. Its statements and definitions are unchanged; the new instance registrations are local to the item. Its unchanged source compiles cleanly against the new item in 9.4 seconds. |

This is the only module returned by `tools/downstream.py` for the item. No
consumer adaptation is needed. The textual hit for the anonymous
`EssentiallySmall` declaration does not name or use a new declaration by name.

## Status

landed 20261021T225155-L-3786911 2026-10-21 (merge of deliver/M6/Sheaf.SixFunctors.CompletedCoefficientFreeResolution)
