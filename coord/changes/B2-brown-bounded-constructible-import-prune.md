# Brown hypotheses public import pruning

## Reason

The old public import of the unpublished six-functor `BoundedConstructible` module pulls in
the SfP1 proof chain and causes unrelated unused-simp diagnostics during delivery. The
Brown module uses only the constructibility predicate and finite-Tor predicate, so their
own defining modules are imported directly. This keeps the public types available while
avoiding the unrelated six-functor implementation dependency.

## Old

```lean
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
```

## New

```lean
public import Sheaf.Paper.CondensedConstantConstructibility
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
```

## Users

| module | group holding it | effect |
|---|---|---|
| `Sheaf.SixFunctorsBasics.BrownHypotheses` | B2 | Direct declarations now import their defining APIs |
| current live direct importers | none | No live current importer; quarantined consumers retain their own imports |

## Status

landed 20261026T180708-L-3375345 2026-10-26 (merge of deliver/B2/Sheaf.SixFunctorsBasics.BrownHypotheses)
