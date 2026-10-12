# AlgebraicGeometry.etaleFieldPointFunctor_essSurj

## Reason
Implement the unchanged theorem with proof-only imports for orbit decomposition and coproduct points.

## Old
```lean
import Sheaf.FieldTheory.EtaleFieldGaloisClassification
import WeilConjectures.Mathlib.RingTheory.Etale.Field
```

## New
```lean
import Sheaf.AlgebraicGeometry.GaloisSetEmbeddingDecomposition
import Sheaf.AlgebraicGeometry.EtaleCoproductEmbeddingPoints
```
The existing theorem signature and local instance attributes are unchanged. These are proof-only imports; no existing public interface changed.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.EtaleFieldPointFunctorEssSurj | E2 | proof implementation and proof-only imports |

## Status
landed 20261012T135228-L-1659698 2026-10-12 (merge of deliver/E2/Sheaf.AlgebraicGeometry.EtaleFieldPointFunctorEssSurj)
