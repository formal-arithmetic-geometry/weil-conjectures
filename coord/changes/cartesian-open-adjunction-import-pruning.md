# CartesianOpenAdjunctionRestriction import pruning

## Reason

The concrete published open mate and its proved normalization suffice. The generic
open/tensor existence theorem is not used by the statement, definitions or proof.
Remove its public import and the two unused private proof imports. No declaration
signature, visibility, attribute or definition body changes.

## Old

```lean
public import Sheaf.SixFunctors.OpenTensorNormalization
import Sheaf.AlgebraicGeometry.ProEtaleInverseImage
import Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral
```

## New

Those three imports are removed. New proof-only imports are:

```lean
import all Sheaf.AlgebraicGeometry.ProEtaleOpenSquareExchange
import all Sheaf.AlgebraicGeometry.EtaleOriginOpenRestrictionTransport
import all Sheaf.AlgebraicGeometry.UnboundedAbelianExchangeComparison
import all Sheaf.AlgebraicGeometry.FixSiteOpenExchangeSheaf
```

The existing public import of `ProEtaleOpenSquareExchange` remains because the public
statements use its concrete constructions. Its additional private `import all` supplies
its proved internal transport calculations to this proof only.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| `Sheaf.SixFunctors.CartesianOpenAdjunctionRestriction` | D5 | Proof completed; unused imports removed. |
| `Sheaf.Paper.IsomorphismFiniteMateNormalization` | K7 (current claim) | No adaptation: it explicitly imports `Sheaf.SixFunctors.OpenTensorNormalization` and uses unchanged public declarations. |

`tools/downstream.py` reports that this is the only downstream module. This change
alters an import edge, not any target statement or a definition used by a target.

## Status

landed 20261024T184848-L-3231955 2026-10-24 (merge of deliver/D5/Sheaf.SixFunctors.CartesianOpenAdjunctionRestriction)
