# Second localization iso proof import

## Reason
The proof of `exists_secondLocalization_iso` uses two auxiliary interfaces in a
plain proof-only import. The delivery therefore changes the module environment
seen while elaborating this module.

## Old
```lean
import Sheaf.Algebra.Homology.DerivedTensorFlatSecondLocalization
```

## New
```lean
import Sheaf.Algebra.Homology.DerivedTensorFlatSecondLocalization
import Sheaf.Algebra.Homology.SecondLocalizationIsoAux
```

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Algebra.Homology.SecondLocalizationIso | N2 | proof uses the auxiliary declarations |

## Status

landed 20261013T224516-L-1474124 2026-10-13 (merge of deliver/N2/Sheaf.Algebra.Homology.SecondLocalizationIso)
