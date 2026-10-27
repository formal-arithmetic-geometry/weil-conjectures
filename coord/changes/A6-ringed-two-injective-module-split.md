# Sheaf.Algebra.Homology.RingedForgetTwoInjectiveHom

## Reason

After abstracting the product-total construction and isolating both sheaf specializations,
the item still took 84 seconds. Its existing definitions and proved representative construction
now live in `Sheaf.Algebra.Homology.RingedForgetTwoInjectiveModels`, which the item publicly
re-exports. The item retains both theorem declarations. Every moved declaration has exactly
the same name, signature, visibility and body. Only its documentation blueprint tag changes.
No mathematical definition, theorem statement, instance, attribute or normalization changes.
No file under WeilConjectures is changed. The new models module uses the default
respectTransparency settings; the original item's existing settings stay in that file.

## Old

The end of the public imports and the existing proof import were:

```lean
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
import Sheaf.Algebra.Homology.QuasiIsoHomComplexMapOfUniverses
```

The representative, comparison, standard-model and native-model declarations were declared
in this item module. Their complete original text is preserved in the new models module.

## New

```lean
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.IsoAlgebra
public import Sheaf.Algebra.Homology.RingedForgetTwoInjectiveModels
```

The QuasiIsoHomComplexMapOfUniverses proof import moves with ringedRepresentatives. The two
new specialization modules are private proof imports of the item. Every original public
import is retained verbatim. All original declarations remain visible to its importers.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Algebra.Homology.RingedForgetTensorTransposition | unclaimed in current local records | Original compiled successfully against delivery; no adaptation needed. |
| Sheaf.Paper.NativeWeilRowHomComparison | unclaimed in current local records | Original compiled successfully against delivery; no adaptation needed. |

| Sheaf.Paper.DerivedWeilOperations | unclaimed in current local records | Indirect user of augmentation; name, signature and body unchanged and re-exported. |
| Sheaf.WeilSheaf.NativeDualRealizationComparisonData | unclaimed in current local records | Indirect user of Comparison; all fields and projections unchanged and re-exported. |
| Sheaf.WeilSheaf.NativeSectionClosedForgetful | unclaimed in current local records | Indirect user of Comparison; all fields and projections unchanged and re-exported. |
| WeilConjectures | unclaimed umbrella module | Indirect user of Comparison; same re-exported declarations; global build belongs to maintainer. |

## Status

landed 20261026T222544-L-667647 2026-10-26 (merge of deliver/A6/Sheaf.Algebra.Homology.RingedForgetTwoInjectiveHom)
