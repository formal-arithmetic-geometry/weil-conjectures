# rhomNormalizedHomProjection: use the existing projection API

## Reason

The unclaimed module `Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses`
exceeded the 60-second compile limit when checked from the current source. Its
private projection recomputed the choice expression behind `homComplexπ`, and
its proofs repeatedly extracted the choice specification. This also made the
item's normalized component comparison expensive to convert.

Use the existing public projection API for the same selected product cone. All
existing declaration signatures, public imports, and public theorem statements
remain identical. No `WeilConjectures` source file is changed. There are no new
holes or data witnesses.

## Old

```lean
private noncomputable def rhomNormalizedHomProjection (A B : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex (R := R) A B).X n ⟶ SheafOfModules.homObj (R := R) (A.X p) (B.X q) :=
  (Classical.choose
    (homComplex_projections_exists.{c, v, max c v r, max c v r} (J := J) (R := R))) A B n p q h
```

## New

```lean
private noncomputable def rhomNormalizedHomProjection (A B : CochainComplex Mod ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (homComplex (R := R) A B).X n ⟶ SheafOfModules.homObj (R := R) (A.X p) (B.X q) :=
  homComplexπ.{c, v, max c v r, max c v r} (J := J) (R := R) A B n p q h
```

The private proof import `HomComplexProjections` is replaced by
`HomComplexComponents`. The limit, differential, and naturality proofs use
`homComplexIsLimit`, `homComplex_d_π`, and `homComplexFunctor_map_f_π` instead of
projecting `Classical.choose_spec`. These are the same cone and laws. The two
projection bodies are definitionally equal. The named limit theorem still proves
the identical proposition, so changing its proof does not change the downstream
choice of an `IsLimit` witness.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.HomComplexGlobalHomotopyOfUniverses | unclaimed | Private projection presentation and three proof bodies use the existing API. |
| Sheaf.Paper.CoefficientHomZeroClass | D4 | Adds a private proof import of the normalized comparison. |
| Sheaf.Algebra.Homology.DerivedInternalHomSectionsModel | K5 | Unchanged public theorem consumer; no adaptation. |
| Sheaf.Algebra.Homology.RhomHypercohomologyBridgeOfUniverses | unclaimed | Unchanged public theorem consumer; no adaptation. |
| Sheaf.CategoryTheory.RingedSiteDualityMaps | Z6 | Unchanged public theorem consumer; no adaptation. |
| Sheaf.CategoryTheory.CoefficientBidualTriangleCompatibility | K3 | Unchanged public theorem consumer; no adaptation. |
| Sheaf.CategoryTheory.RelativeBidualTriangles | unclaimed | Unchanged public theorem consumer; no adaptation. |
| Sheaf.Paper.DualityPairing | S1 | Unchanged public theorem consumer; no adaptation. |

The private projection name occurs only in its defining module. Existing importers
use its unchanged public theorem. The item adds the private comparison consumer.
The projection bodies are checked by `rfl`; no consumer adaptation is required.
The DAG proof at `lem-pur-hom-complex-global-homotopy` already uses the same
projection node and mathematical route, so its statement and dependencies stay.

## Status

landed 20261020T233114-L-894219 2026-10-20 (merge of deliver/D4/Sheaf.Paper.CoefficientHomZeroClass)
