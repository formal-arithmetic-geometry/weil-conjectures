# AlgebraicGeometry.ProEtale.IsomorphismScalarTensor.completed_formula_chain_data

## Reason

The previous statement identified a map on termwise inverse-image complexes with
one on strict quotient Roos complexes by HEq, without the two endpoint transports.
They are different chain models. For example, with identity scheme and scalar
maps and a nonzero free module in degree zero, the Roos model also has a nonzero
shifted product term. Its augmentation has zero shifted coordinate; it is not an
isomorphism of complexes, even when it becomes an isomorphism after localization.
Moreover, the good-complex subcategory requires flat terms and K-flatness, not
completeness. The strict-cone naturality theorem therefore cannot supply this HEq.

Replace this incorrect intermediate statement by the sheaf tensor isomorphism
and its local pure-tensor rule from Stacks Tag 03EL. Apply it in every cochain
degree in the sole caller, preserving that caller's statement exactly. The new
proof uses the normalized ordinary scalar adjunction and the proved generic
adjunction-square construction from LimitScalarChainComparison. It does not
assume the new comparison or select arbitrary data from an existence axiom.

All new helpers are private and proved. The new helper instances are private and local;
reducibility controls are local to this module. No definition used by a target changes. No file under
lean/WeilConjectures is modified. This is a statement repair, not a proof of the
old HEq assertion.

The unused public import ScalarPullbackStrictConeData and private import
ScalarPullbackStrictConeNaturality are removed from the item. The parent's
private import IsomorphismScalarCompletedFormulaChainNormalization is removed.
That module is held by P1 and remains untouched; it is no longer on this parent's
proof route. No unit statement or realized proof step is bypassed.

## Old

```lean
theorem completed_formula_chain_data
    (_hX : ∀ x : X, IsUnit (l : X.presheaf.stalk x))
    (_hY : ∀ y : Y, IsUnit (l : Y.presheaf.stalk y)) :
    ∃ D : ScalarPullbackStrictConeData l E L ι g,
      ∃ b : (integralOperationsGoodComplex l E Y).ι ⋙ leftComplex l E L ι g ≅
        (integralOperationsGoodComplex l E Y).ι ⋙ rightComplex l E L ι g,
        (∀ P : (integralOperationsGoodComplex l E Y).FullSubcategory,
          HEq (b.hom.app P)
            ((scalarPullbackConeMap l E L ι g D.level D.cone).app P.obj))
```

## New

```lean
theorem completed_formula_chain_data :
    ∃ b : inverseImageIntegralModules l E g ⋙ completedOrdinaryScalarExtension l E L ι X ≅
        completedOrdinaryScalarExtension l E L ι Y ⋙ inverseImageIntegralModules l L g,
      ∀ (M : integralTowerModules l E Y) (U : X.ProEt)
        (p : M.val.obj (op ((proEtaleIsoPostcompose g).obj U)))
        (a : (completedIntegralCommRingSheafUnrestricted l L Y).obj.obj
          (op ((proEtaleIsoPostcompose g).obj U))),
        (b.hom.app M).val.app (op U)
          (completedScalarTensorSection l E L ι X
            ((inverseImageIntegralModules l E g).obj M) (op U)
            ((inverseImageCompletedCoefficientMap l L g).hom.app (op U) a) p) =
          completedScalarTensorSection l E L ι Y M
            (op ((proEtaleIsoPostcompose g).obj U)) a p
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IsomorphismScalarCompletedFormulaChainData | N4 | The incorrect intermediate statement is replaced and fully proved. |
| Sheaf.Paper.IsomorphismScalarCompletedModelFormula | unclaimed (server checked 2026-10-28) | Sole caller; its statement and visibility are unchanged. The proof applies the sheaf isomorphism degreewise and restricts it to good complexes. |
| Sheaf.Paper.IsomorphismScalarCompletedModel | unchanged validation consumer | Direct importer of the adapted parent; no declaration or proof change is required. |

The source scan tools/downstream.py --uses completed_formula_chain_data found
only the item and its adapted parent mentioning the changed declaration.
The sole direct importer of the item is that parent. The sole direct importer
of the parent is IsomorphismScalarCompletedModel. The normalization module does
not import the item or mention its changed declaration.

## Status

landed 20261028T055727-L-801409 2026-10-28 (merge of deliver/N4/Sheaf.Paper.IsomorphismScalarCompletedFormulaChainData)
