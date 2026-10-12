# AlgebraicGeometry.Scheme.nonempty_freeSheafDerivedSectionsIso proof context

## Reason

The explicit proof adds scoped namespace, universe, variable, open, include and omit
commands around private comparison helpers. The static interface checker classifies
these context commands as a visible change and requires this record. All added
constructions and lemmas are private. Their namespaces close before the unchanged
public theorem, and their variables do not enter its signature. Open commands only
affect name resolution while elaborating this file; they do not export an altered
mathematical definition, instance, notation or theorem statement to its importers.
The only public declaration remains the original theorem with the original signature.

## Old

```lean
universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme
```

These were the only context commands before the public theorem. Its full signature
is unchanged in the delivery.

## New

The original context remains. Before the original public theorem, one closed
`FreeSheafComparisonAux` namespace block and a closed `AlgebraicGeometry.Scheme`
namespace block contain only private helpers. The additional context commands are
`open CochainComplex HomComplex`,
`open CochainComplex HomComplex Limits Opposite`, and scoped
`variable`, `include`, and `omit` commands supplying the helper category and functor
parameters. All helper definitions have explicit data and all helper lemmas are proved.
A proof-only `import all Sheaf.AlgebraicGeometry.EtaleSheafHExtDerivedComparison`
reuses its private generic postcomposition constructions and naturality proofs;
these imported helpers are not re-exported. The returned duplicate helper blocks
are deleted entirely; no interface of the imported module changes.
The public theorem's parameters, universes and conclusion are identical to the old ones.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf | J1 (recorded in existing project change record) | Calls the unchanged theorem at degree n; no adaptation needed. |

Repository search finds this one direct caller, which selects the natural isomorphism
from the Nonempty result. The downstream script with the theorem's short name printed
no additional users. No target statement or underlying definition is changed, so no
statement correction or target re-review is required.

## Status

landed 20261012T135258-L-1680624 2026-10-12 (merge of deliver/N3/Sheaf.AlgebraicGeometry.EtaleFreeSheafDerivedSections)
