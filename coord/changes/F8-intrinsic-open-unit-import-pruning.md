# Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit imports

## Reason

The proof uses only the intrinsic adjunction and the existing fixed-scalar
full-faithfulness theorem. The direct-image module supplies nothing used by its
statement or proof, so remove that public import as required by stage-3 pruning.
No declaration signature, definition, instance or target changes.

## Old

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
public import Sheaf.AlgebraicGeometry.ProEtaleFiniteCoefficientDirectImage
```

## New

```lean
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZeroAdjunction
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.FullyFaithful
```

## Users

`tools/downstream.py Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit --uses
sfIntrinsicOpenUnit_isIso` reports one downstream consumer. Both it and the item
compile through `lcompile.py --all` against the changed item. The consumer is
byte-for-byte unchanged and is not delivered. Its existing public import of
`SfIntrinsicRealizationTransport` already supplies the direct-image module through
`ProEtaleIntrinsicFiniteOperations`.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit | F8 | One hole proved; unused public import removed. |
| Sheaf.AlgebraicGeometry.ProEtaleProperOpenSheafComparison | unclaimed | No adaptation needed; unchanged consumer compiles against the new imports. |

## Status

landed 20261018T145100-L-3639187 2026-10-18 (merge of deliver/F8/Sheaf.AlgebraicGeometry.ProEtaleIntrinsicOpenUnit)
