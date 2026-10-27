# SheafOfModules.DerivedTensorConstraints.complexMonoidal and complexMonoidalStruct

## Reason

Native complex tensor dictionaries were repeatedly synthesized while comparing the
published representative formulas with natural functor comparisons. Explicitly naming
the same native dictionaries keeps their specialization consistent across the formulas
and proofs. The preliminary constructor check alone took 53.2 seconds; the complete
file must also check the localization extensions and normalization equalities.

## Old

Neither abbreviation existed. Tensor notation used the native instances directly:

```lean
HomologicalComplex.monoidalCategory (Modules R) (.up ℤ)
HomologicalComplex.monoidalCategoryStruct (Modules R) (.up ℤ)
```

The source text of all existing public signatures and definition bodies is preserved.

## New

```lean
abbrev complexMonoidal : MonoidalCategory (Complex R) :=
  HomologicalComplex.monoidalCategory (Modules R) (.up ℤ)

abbrev complexMonoidalStruct : MonoidalCategoryStruct (Complex R) :=
  HomologicalComplex.monoidalCategoryStruct (Modules R) (.up ℤ)

attribute [local instance 4001] complexMonoidal complexMonoidalStruct
```

These are transparent abbreviations of the existing Mathlib constructions, not new
choices of tensor data. Local priorities prefer these dictionaries when elaborating
this module. Their object, morphism, unit and associator data are definitionally the
same native data. The published derived tensor and representativeIso are unchanged.
No target statement changes, and no mathematical definition used by a target changes
meaning. Independent review should check that the abbreviations expand to exactly
the original native instances.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints | P3 | Uses the two abbreviations locally while proving its four original statements. |

The downstream script lists no consumers, and searching the Lean library finds no
external importer or declaration use. No module needs adaptation. The DAG parent
still cites the assigned node and is preserved. No source-library file is edited.

## Status

landed 20261022T032609-L-2043010 2026-10-22 (merge of deliver/P3/Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints)
