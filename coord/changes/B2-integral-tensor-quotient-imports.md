# SheafOfModules.integral_tensor_quotient_epimorphism

## Reason

Both original holes are proved using the existing scalar-extension construction and Mathlib.
The former public imports expose unrelated site-covering, category and independent-universe
tensor APIs. Replace them with the direct upstream construction import. No declaration,
signature, definition body or instance changes. The only visibility change is the removal
of these unused transitive re-exports. The current direct consumer compiles unchanged.
Two proof-only imports added since the earlier attempt are also removed.

## Old

```lean
public import Sheaf.CategoryTheory.SiteCoveringAxioms
public import Sheaf.CategoryTheory.RingedSiteModules
public import Sheaf.Algebra.Category.ModuleCat.Sheaf.SiteTensorFunctoriality
public import Mathlib.CategoryTheory.Sites.EpiMono
import Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.AlgebraicGeometry.SiteSheafificationSectionsLocal
```

## New

```lean
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
```

## Users

`python3 tools/downstream.py Sheaf.SixFunctors.IntegralTensorQuotientEpimorphism`
reports 305 transitive import consumers. Source inspection identifies `Sheaf.SixFunctors.IntegralLisseReductionEquivalence` as a direct
consumer, via a proof-only import that does not re-export this item. The only downstream.py
`--uses integralTensorQuotientUnit integral_tensor_quotient_epimorphism` name hits are in
the item itself. The direct consumer was checked unchanged with lcompile.py against the reduced-import module:
exit code 0, item 5.2 seconds, consumer 7.5 seconds. It directly imports the module
category API it needs, and no removed re-export is necessary for its elaboration.
No consumer adaptation or target meaning change is necessary.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.IntegralTensorQuotientEpimorphism | B2 | Two proofs completed; unused public re-exports removed; all four declaration signatures unchanged. |
| Sheaf.SixFunctors.IntegralLisseReductionEquivalence | not adapted | Unchanged; compiled against the reduced imports. |

## Status

landed 20261019T002504-L-2140983 2026-10-19 (merge of deliver/B2/Sheaf.SixFunctors.IntegralTensorQuotientEpimorphism)
