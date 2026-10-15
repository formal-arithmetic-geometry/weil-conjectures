# Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution imports

## Reason

The proof does not use `Mathlib.Algebra.Homology.DerivedCategory.Basic`; the target interfaces
are supplied by `Mathlib.Algebra.Homology.CochainComplexPlus`. Removing the redundant public
import keeps the dependency closure smaller.

## Old

`public import Mathlib.Algebra.Homology.DerivedCategory.Basic`

## New

The import line is removed. No declaration signature or definition changes.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution | D4 | Compiles unchanged; uses `CochainComplexPlus` for `QuasiIso` and `Plus`. |

## Status

landed 20261015T190716-L-966222 2026-10-15 (merge of deliver/D4/Sheaf.Algebra.Homology.FunctorialBoundedInjectiveResolution)
