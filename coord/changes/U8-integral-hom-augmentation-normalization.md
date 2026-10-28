# WeilConjectures.IntegralHom.reductionTower_components_augmentation

## Reason

The quantified family θ is tied only to the transitions, not to the fixed e or
the quotient units. Replacing θ by -θ preserves all its hypotheses and changes
its augmentation composite. For ell=3 and nonzero coefficient-unit reductions,
2 is invertible and these composites cannot both equal the fixed quotient unit.
Thus this split is false, as the landed STATEMENT-DISPUTED marker records.

The parent needs existence of one normalized family. Construct that family and
both equations together using the signed comparison on a common coefficient
tower. The representation theorem must retain the coefficient-unit maps and
normalization at R[0], which the previous separate tensor-model statement omits.
The existing tensor-model module is held by H1 and is unchanged. The missing
normalized representation is a new strictly lower statement, with one hole.
It does not assert a comparison at any quotient level or its invertibility.

## Old

```lean
theorem reductionTower_components_augmentation
    (K : completedIntegralDerivedCategory l E Y D hl)
    (P G P' G' : CochainComplex (completedIntegralModuleSheaves l E Y D hl) ℤ)
    (q : P ⟶ G) (q' : P' ⟶ G')
    (hq : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q)
    (hq' : CochainComplex.IsKFlatResolutionIndependentCoefficients
      (J := AlgebraicGeometry.Scheme.ProEt.topology Y)
      (R := completedIntegralCommRingSheaf l E Y D hl) q')
    (e : DerivedCategory.Q.obj G' ≅
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl)).obj
        (op K, DerivedCategory.Q.obj G)) :
    let H := (Functor.curry.obj
      (hom.{t, u} Y (completedIntegralCommRingSheaf l E Y D hl))).obj (op K)
    ∀ (θ : ∀ n : ℕ, H.obj ((integralReductionTower l E Y D hl P).obj (op n)) ≅
        (integralReductionTower l E Y D hl P').obj (op n)),
      (∀ n : ℕ,
        H.map ((integralReductionTower l E Y D hl P).map (homOfLE n.le_succ).op) ≫
            (θ n).hom =
          (θ (n + 1)).hom ≫
            (integralReductionTower l E Y D hl P').map (homOfLE n.le_succ).op) →
      ∀ n : ℕ,
        e.inv ≫ (integralReductionTowerCone l E Y D hl q' hq').π.app (op n) =
          H.map ((integralReductionTowerCone l E Y D hl q hq).π.app (op n)) ≫
            (θ n).hom
```

The parent chose θ using reductionTower_components_transition and applied this
false universal theorem to it.

## New

Withdraw lean/Sheaf/Paper/IntegralHomReductionTowerAugmentation.lean through
deleted.txt; the landing writes an empty module. Its DAG node is retained,
its Lean attachment is null and its parent no longer cites it.

The exact signature of reductionTower_components is unchanged. Its proof now
obtains separate unit-normalized models, constructs the natural signed chain
comparison, proves its quotient components invertible using the existing
two-term criterion, and conjugates its inverse by the model isomorphisms.
Naturality gives the transition equation. Naturality for R[0] -> Q_n and the
normalization at R[0] give the augmentation equation for that same family,
after cancelling the two component isomorphisms.

The new representation theorem is reductionTower_unit_models in
Sheaf.Paper.IntegralHomReductionTowerUnitModels, node
lem-sf-integral-hom-tower-unit-models. Its exact Lean statement is recorded in
that node. Its separate isomorphisms preserve their respective augmentations,
and only the signed map at the coefficient unit is normalized. The comparison
and invertibility at the actual quotient levels are proved in the parent.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralHomReductionTowerAugmentation | U8 | False split withdrawn; node retained without a Lean attachment. |
| Sheaf.Paper.IntegralHomReductionTowerComponents | unclaimed | Only user of the removed declaration; complete replacement proof and private naturality helper, with identical signature and public import. |
| Sheaf.Paper.IntegralHomAugmentedTowerComparison | unclaimed | Direct consumer of Components; no source or statement change; compiled against the replacement. |

The declaration-use search finds only the withdrawn module and Components.
Components independently imports IntegralHomReductionModels publicly, so removing
the obsolete proof import loses no public interface used by its consumers.
No definition, instance, attribute, target statement or target meaning changes.
The unit record sk-prop-sf-biduality-general has no realization attached to the
withdrawn split; the finite-free coefficient route remains the same.

## Status

landed 20261028T072456-L-1952983 2026-10-28 (merge of deliver/U8/Sheaf.Paper.IntegralHomReductionTowerAugmentation)
