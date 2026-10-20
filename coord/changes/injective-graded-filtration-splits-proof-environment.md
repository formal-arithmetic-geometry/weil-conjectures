# Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits proof environment

## Reason

Stage-3 preflight classifies the section and variable commands used for private
finite-tail helpers as a module-environment change and requires this record.
These helpers implement the coordinate-extension proof. No existing public
signature, definition, instance, notation, option, or attribute changes.

## Old

Immediately after `namespace CategoryTheory.FilteredObject`, the original file
had only the public theorem, with proof `by sorry`. It had no helper section.

## New

Before that theorem the file now has private declarations `Tail`, `tailFamily`,
`tailInclusion`, `tailRetraction`, `tailComplex`, and `tail_shortExact`. Their
shared parameters are scoped as follows:

```lean
section Tail

variable {C : Type u} [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]
  {a b : ℤ} (J : Set.Icc a b → C)

-- private helper declarations

end Tail
```

Noncomputability is marked on the individual private constructions. The finite
biproduct instance of the main proof is a local `let` inside its theorem body.
There is no new `noncomputable section` or local instance attribute. The public
theorem's signature and visibility are identical. All added helpers are private
and proved. The only removed import is a redundant proof-only import.

## Users

`tools/downstream.py Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits
--uses CategoryTheory.FilteredObject.injective_graded_filtration_splits` finds
87 transitive importers and no textual use of the theorem outside its own
module in the current shared snapshot. The section is closed before the
existing theorem, so importers see the same public interface and require no
adaptations. No other group's files are changed.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits | V3 | private helper scope; public signature unchanged |

## Status

landed 20261020T131209-L-1258112 2026-10-20 (merge of deliver/V3/Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits)
