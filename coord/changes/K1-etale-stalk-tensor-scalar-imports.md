# Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar public imports

## Reason

The stalk theorem needs the module-category tensor instances, the strong monoidal point
fiber functor, and module-valued sheafification. It does not need the geometric pullback
construction exported by the broad stalk-monoidal module. Replace that public import by
the smaller imports providing the monoidal colimit instances used in the unchanged theorem
signatures. No declaration signature or definition changes.

## Old

```lean
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal
```

## New

```lean
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
```

All other original public imports remain. The three newly added proof-only imports are
`Sheaf.Algebra.Category.ModuleCat.RingScalarExtension`,
`Mathlib.CategoryTheory.Sites.Adjunction`, and
`WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal`.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar | K1 | All seven signatures unchanged; all seven holes proved. Remote compile and individual axiom audits pass. |
| Sheaf.Paper.LisseTensorScalarExtension | J2 | Direct importer, proof-only. Compiled its original source unchanged against the new module; it already publicly imports StalkMonoidal independently. |
| Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine | D2 | Direct importer, proof-only. Compiled its original source unchanged against the new module. |

`tools/downstream.py ... --uses` for all seven declaration names finds only this module
itself as a textual user. Its two direct importers are listed above and were checked as
well because the change concerns exported imports. Neither re-exports this module. No
consumer source file is changed or delivered. No target definition changes, so the meaning
of the targets is unchanged and no target-statement review is reopened.

## Status

landed 20261018T062819-L-658933 2026-10-18 (merge of deliver/K1/Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar)
