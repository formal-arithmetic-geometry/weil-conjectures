# AlgebraicGeometry.ProEtale.IntegralDirectImageTower.Evaluation.derived

## Reason

Restore the quarantined module and repair its recorded global-build failure at the
construction of the derived evaluation comparison. The existing `hAdd` proof is a
plain local let, so typeclass inference cannot use it while elaborating the
composition of derived natural isomorphisms. Register the very same proof as a
local instance with `letI`. This changes no mathematical construction, public type,
attribute, import, or normalization equation. No target meaning changes.

## Old

```lean
def Evaluation.derived (s : Presentation l E) (e : Evaluation l E s)
    (T : Scheme.{u}) (n : ℕ) :
    (realization l E s T).functor ⋙ SpTowerShriek.Ev l E T n ≅
      spDerivedCoefficientEvaluation l E T (s.towers T) n :=
  letI := (s.towers T).hasDerived
  letI := s.base.realizationAdditive T
  letI := (s.towers T).equivalenceAdditive
  letI := (s.towers T).evaluationLimits n
  letI := (s.towers T).evaluationColimits n
  let hAdd : (spCoefficientEvaluation l E T (s.towers T).equivalence n).Additive := by
    letI := (s.towers T).equivalenceAdditive
    letI := (s.towers T).evaluationLimits n
    exact Functor.additive_of_preserves_binary_products _
  letI : ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n).Additive := by
    infer_instance
  letI : PreservesFiniteLimits ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n) := by
    infer_instance
  letI : PreservesFiniteColimits ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n) := by
    infer_instance
  let e' : (s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n ≅
      spCoefficientEvaluation l E T (s.towers T).equivalence n := e.ordinary T n
  (Functor.mapDerivedCategoryCompIso (s.base.realization T).functor
      (SpTowerShriek.ev l E T n)).symm ≪≫
    @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
      ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n)
      (spCoefficientEvaluation l E T (s.towers T).equivalence n)
      _ hAdd _ _
      ((s.towers T).evaluationLimits n) ((s.towers T).evaluationColimits n) e'
```

## New

```lean
def Evaluation.derived (s : Presentation l E) (e : Evaluation l E s)
    (T : Scheme.{u}) (n : ℕ) :
    (realization l E s T).functor ⋙ SpTowerShriek.Ev l E T n ≅
      spDerivedCoefficientEvaluation l E T (s.towers T) n :=
  letI := (s.towers T).hasDerived
  letI := s.base.realizationAdditive T
  letI := (s.towers T).equivalenceAdditive
  letI := (s.towers T).evaluationLimits n
  letI := (s.towers T).evaluationColimits n
  letI hAdd : (spCoefficientEvaluation l E T (s.towers T).equivalence n).Additive := by
    letI := (s.towers T).equivalenceAdditive
    letI := (s.towers T).evaluationLimits n
    exact Functor.additive_of_preserves_binary_products _
  letI : ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n).Additive := by
    infer_instance
  letI : PreservesFiniteLimits ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n) := by
    infer_instance
  letI : PreservesFiniteColimits ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n) := by
    infer_instance
  let e' : (s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n ≅
      spCoefficientEvaluation l E T (s.towers T).equivalence n := e.ordinary T n
  (Functor.mapDerivedCategoryCompIso (s.base.realization T).functor
      (SpTowerShriek.ev l E T n)).symm ≪≫
    @Functor.mapDerivedCategoryNatIso _ _ _ _ _ _ _ _
      ((s.base.realization T).functor ⋙ SpTowerShriek.ev l E T n)
      (spCoefficientEvaluation l E T (s.towers T).equivalence n)
      _ hAdd _ _
      ((s.towers T).evaluationLimits n) ((s.towers T).evaluationColimits n) e'
```

## Users

The six direct importers listed by `tools/downstream.py` are below. Its transitive
importer list is the same in the current restored source snapshot. Claims were
checked on the project server; none of these six modules is held. The repaired
item is held by B4. No importer mentions the changed local binding, and every
public declaration has the same name and type. The node
`def-sp-integral-direct-image-tower-data` keeps its attachment and dependencies;
the proof route and all coefficient constructions are unchanged.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.IntegralTowerCompactificationCoherence | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.IntegralTowerGeometryLimits | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.IntegralTowerImageReconstruction | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.IntegralTowerProjectionMates | unclaimed | Same public interface; no adaptation. |
| Sheaf.Paper.IntegralTowerPullTensorConstructible | unclaimed | Same public interface; no adaptation. |

All six original importers are compiled individually against the repaired item
before delivery. Their temporary sandbox copies are removed after verification.

## Status

landed 20261027T194426-L-824169 2026-10-27 (merge of deliver/B4/Sheaf.Paper.IntegralDirectImageTowerData)
