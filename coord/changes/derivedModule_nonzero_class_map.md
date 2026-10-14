# derivedModule_nonzero_class_map

## Reason

The original target had a single proof hole. Stage 3 exposes the chain-level
cycle-to-derived-map step as a separate named theorem so the remaining gap is
tracked by its own DAG node. Its statement is needed by the target proof and is
a strictly intermediate step: the degree and nonzero homology class are already given.

## Old

No declaration existed in `Sheaf.CategoryTheory.DerivedModuleRankOneNonzeroMap`.

## New

A new declaration in `Sheaf.CategoryTheory.DerivedModuleNonzeroClassMap`:

```lean
theorem derivedModule_nonzero_class_map
    {S : Type w} [Ring S]
    [HasDerivedCategory.{max w vH} (ModuleCat.{max w vH} S)]
    [HasCoproducts.{max w vH} (DerivedCategory (ModuleCat.{max w vH} S))]
    (K : DerivedCategory (ModuleCat.{max w vH} S)) (n : ℤ)
    (x : ((DerivedCategory.homologyFunctor
      (ModuleCat.{max w vH} S) n).obj K)) (hx : x ≠ 0) :
    ∃ f :
      (DerivedCategory.singleFunctor (ModuleCat.{max w vH} S) 0).obj
        (ModuleCat.of S (ULift.{vH} S)) ⟶ K⟦n⟧, f ≠ 0
```

The existing item's signature and public imports are unchanged. It adds proof-only
imports of this module and the upstream homology zero criterion. The new module's
public imports are ModuleCat.Abelian, Module.ULift and the Mathlib derived homology
sequence; these supply its statement. No existing definition changes, and no target
statement requires renewed semantic review.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.CategoryTheory.DerivedModuleRankOneNonzeroMap | H3 | target proof applies the intermediate theorem |

## Status

landed 20261014T020512-L-3811774 2026-10-14 (merge of deliver/H3/Sheaf.CategoryTheory.DerivedModuleRankOneNonzeroMap)
