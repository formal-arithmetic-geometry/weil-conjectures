# SheafOfModules.CommonQuotientReduction.Comparison

## Reason

The item timed out while elaborating generated structure support and proof terms. The unused
public imports were already identified as removable by its statement review. Removing them
and suppressing optional structure generators avoids unfolding unrelated tensor universes.
The handwritten public declarations, their types, all structure fields and their defining terms
stay intact.

## Old

```lean
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import Sheaf.Paper.RingedTopoiTensorSections
```

The default `genSizeOf`, `genSizeOfSpec`, and `genInjectivity` options were enabled.

## New

These two imports are removed. The file sets `genSizeOf`, `genSizeOfSpec`, and
`genInjectivity` to `false` and makes `monoidalCategory` locally irreducible for its proofs.
The pure-section definition is locally irreducible while elaborating `Comparison`
and then restored for the supporting proofs. K-flatness and site flatness predicates
remain locally irreducible, with explicit unfolding at their elimination steps.
Exact restriction reuses the existing coefficient-change lemma, its instances are
supplied explicitly, and ordinary braiding orders tensor cancellation before totalization. All required statement imports remain; new proof dependencies are private imports.
No existing mathematical declaration changes signature or definition.

## Users

`python3 tools/downstream.py Sheaf.Paper.FlatCommonQuotientReductionTower --uses
SheafOfModules.CommonQuotientReduction.Comparison` now reports one downstream module,
`Sheaf.Paper.DerivedFiniteQuotientCoherence`; the only uses of `Comparison` are in
the item module itself.
A current direct-import search finds `Sheaf.Paper.DerivedFiniteQuotientCoherence`.
It explicitly imports `RingedTopoiTensorSections` itself and does not refer to
`CommonQuotientReduction.Comparison`; its needed declarations are unchanged.
DAG parents are retained:
this is an implementation of their needed statement, not a withdrawal.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FlatCommonQuotientReductionTower | T5 | proof and elaboration changes only |
| Sheaf.Paper.DerivedFiniteQuotientCoherence | unclaimed in local claim records | no source change; imports tensor sections directly and uses no changed declaration |

No target statement or definition used by a target changes meaning.

## Status

landed 20261021T120555-L-3913330 2026-10-21 (merge of deliver/T5/Sheaf.Paper.FlatCommonQuotientReductionTower)
