# Explicit parameters in ordinary signed-line scalar comparison

## Reason

The complete proof of `comparison_identity_arbitrary` exposed a file-time problem.
Profiling showed repeated category-instance searches and unfolding of identical-looking
single complexes and tensor expressions. Make the existing universe arguments and the
localization functors' base categories explicit. Keep the actual functors, maps, section
formulas, hypotheses and conclusions unchanged.

## Old and new

The ordinary and derived tensor aliases still expand to exactly the constants printed
by Lean for their original definitions:

```lean
LineUnbounded.tensor.{t, a} X R (power.{t, a} L m)
LineUnbounded.derived.{t, a, w} X R (power.{t, a} L m)
```

The code now supplies these universe arguments at concrete use sites. The `compute`
definition still consists, in the same order, of the derived image of the inverse source
quotient comparison, the presentation counit, the homotopy-category factor map, and the
target quotient comparison. Its source comparisons explicitly use `Modules X R`; its
target comparisons explicitly use `Modules X S`. Thus these are annotations of the
existing construction, rather than a new computation map.

The public signatures retain the same mathematical types. No definition is replaced by
existence or choice, and no hypothesis is added. No target meaning changes. The existing category
and abelian caches remain active.
The monoidal cache declaration remains intact but is deactivated locally in favor of
its canonical underlying tensor instance, which is registered locally. The site-specific
`hasSheafify_proEtTopology` instance requires coefficient hom-universe `t + 1`, so it
is disabled locally for this independent-coefficient module; existing general
sheafification instances supply `max a (t + 1)`. No new public cache declarations are
added. Local `𝒬[R]` notation expands to `DerivedCategory.Q (C := Modules X R)` and is
not exported. The K-flat flat-term proof transports exactness through the existing
site tensor comparison, with explicit types for its two preservation properties and
Mathlib's finite-limit/colimit composition lemmas.

## Users

`tools/downstream.py --uses compute` finds only this item's uses of `compute`, among the
91 transitive importers reported at the time of checking. The direct consumer
`Sheaf.Paper.FlatLineDerivedReduction` uses the existing line-data, tensor and twist
interfaces with explicit universe arguments. Their construction data and types are
unchanged, so no consumer adaptation is required. No source-library file is changed.

The affected module is `Sheaf.Algebra.Homology.OrdinaryLineDerivedScalarComparison`,
held by J4. Its existing parameters are made explicit and one original hole is proved.

## Status

landed 20261026T023349-L-548953 2026-10-26 (merge of deliver/J4/Sheaf.Algebra.Homology.OrdinaryLineDerivedScalarComparison)
