# AlgebraicGeometry.ProEtale.SmoothPurityBaseChange.towerGamma

## Reason

The tower-factors proof passed elaboration but kernel checking took about 39 seconds,
and the whole file exceeded 60 seconds. The previous definition of towerGamma
eliminated a compactification record and returned SpTowerGamma.gamma after transport.
Its source is already the ordered tensor source, and the definition of that published
gamma is orientation followed by the tensor mate. Construct this composite directly
using the existing towerTensorMap. This avoids an unnecessary dependent case-split
term at every use of towerGamma. The generic tensor_factors_compose helper separately
keeps the proof calculation independent of the tower implementations.

## Old

```lean
def towerGamma (P : TowerPurityAt ell E b o q c d w hF G adj lv)
    (K : SpTowerCalculus.C ell E b q Y) :
    (SpTowerGamma.source ell E b o q f w d).obj K ⟶
      (SpTowerGamma.exceptional ell E b q G).obj K := by
  rcases c with ⟨Z, p, j, rfl, hp, hj⟩
  exact SpTowerGamma.gamma ell E b o q (SpTowerGamma.factorization j p)
    w d P.tensorX P.tensorY hF G adj P.unit_mem P.orientation K
    (P.tensor_mem K) (P.projection_iso K)
```

## New

```lean
def towerGamma (P : TowerPurityAt ell E b o q c d w hF G adj lv)
    (K : SpTowerCalculus.C ell E b q Y) :
    (SpTowerGamma.source ell E b o q f w d).obj K ⟶
      (SpTowerGamma.exceptional ell E b q G).obj K :=
  (SpTowerShriek.tensor ell E b X).map (Prod.mkHom (𝟙 _) P.orientation.hom) ≫
    towerTensorMap ell E b o q c d w hF G adj lv P K
```

The two constructions are equal: the prior towerGamma_eq API, compiled successfully
before this optimization, already proved exactly this factor formula. Its proof
eliminates c as in the old body and closes by rfl, since the new body is the defining
formula of SpTowerGamma.gamma.
No orientation, tensor mate, comparison or adjunction was changed. In particular,
the hypothesis and conclusion of tower_factors and every target retain their meaning.
The existing towerGamma_eq API is now rfl without a dependent elimination.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.SmoothPurityBaseChangeFactors | C3 | Uses the same map and factor expansion; optimized kernel term. |
| Sheaf.Paper.TowerFactorOrientation | C3 (new) | Imports the data; does not mention towerGamma. |
| Sheaf.Paper.TowerFactorTensor | C3 (new) | Imports the data; does not mention towerGamma. |
| Sheaf.Paper.FinitePurityCounitSystem | unclaimed in current local claim records | Sole existing direct importer of the original module; it uses finite maps, not towerGamma. Its unchanged source is compiled against the new definition. |

A repository-wide search finds no other consumer of
SmoothPurityBaseChange.towerGamma outside its original definition and theorem module
(the ProEtaleCompositionTower modules have an unrelated namespaced homonym). The original module continues to
publicly reexport the same constant with the same signature.

## Status

landed 20261027T021300-L-2752542 2026-10-27 (merge of deliver/C3/Sheaf.Paper.SmoothPurityBaseChangeFactors)
