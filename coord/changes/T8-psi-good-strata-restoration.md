# AlgebraicGeometry.OrientedNearbyCycles.PsiGoodStrata.exists_constructible_cohomology_strata

## Reason

Restore the module assigned in coord/rework.tsv from its quarantine archive. The latest
recorded global build failed at the two occurrences of the retired
`Scheme.LocallyClosedStratification` name. The retirement record
`coord/changes/F9-retire-locally-closed-stratification.md` identifies that name as an
abbreviation of `Scheme.Stratification`. Use its defining type directly, retaining
all binders, constructibility conjuncts, immersions and local trivializations.

## Old

```lean
public import Sheaf.AlgebraicGeometry.LocallyClosedStratification
```

The affected conclusion binders were:

```lean
    ∃ (A : Scheme.LocallyClosedStratification X) (B : Scheme.LocallyClosedStratification S),
```

The retired declaration was:

```lean
abbrev LocallyClosedStratification (X : Scheme.{w}) := Stratification X
```

## New

```lean
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
```

The conclusion binders now expand that abbreviation:

```lean
    ∃ (A : Scheme.Stratification X) (B : Scheme.Stratification S),
```

The full statement is otherwise unchanged. This is a name port with the same elaborated
meaning, not a change to the geometric stratification condition. No target statement or
public definition changes. The DAG Lean signature uses the current spelling.

Additionally, the existing theorem `upContinuous` is proved by the Mathlib equivalence
instance for the topology induced by `AsSmall.down`. This adds the private proof import
`Mathlib.CategoryTheory.Sites.Equivalence`, with no signature or instance change.

## Users

`tools/downstream.py ... --allow-missing --uses exists_constructible_cohomology_strata
upContinuous` reports zero live downstream modules, because the item is quarantined.
Searching both `lean/` and `quarantine/` finds the following preserved consumer.

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.NearbyCycleSheafFiniteness | unclaimed, quarantined | Imports the item for its unfinished proof; no explicit use of a changed name. Its theorem signature and proof are unchanged; no adaptation required. |

The consumer's own quarantine repair is outside this packet. Its dependency and the item's
DAG attachment remain intact. The parent node lem-trf-nearby-cycle-sheaf-finiteness still
needs the restored item. No withdrawal or dependency pruning is performed.

## Status

landed 20261024T020615-L-2626221 2026-10-24 (merge of deliver/T8/Sheaf.Paper.PsiGoodOrientedCohomologyStrata)
