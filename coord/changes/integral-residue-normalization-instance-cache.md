# AlgebraicGeometry.ProEtale.CondensedRing.integralResidue_projection_normalization

## Reason

The proof needs a compact name for the existing integral derived monoidal instance.
The uncached statement alone took 33.7 seconds of kernel checking, and complete
compilations approached or exceeded 60 seconds. A named instance, definitionally
equal to the existing one and instance_reducible for consumer typeclass matching,
reduces full compilation to about 20 seconds. The module publicly imports this
new API because the named instance occurs in its elaborated statement. Added
private generic proof helpers also add local namespace, universe and variable
commands. These elaboration changes are recorded even though the theorem signature
is textually unchanged and its mathematical meaning is unchanged.

## Old

```lean
public import Sheaf.Paper.IntegralResidueComparisonInterface
public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
```

The original signature, verbatim:

```lean
theorem integralResidue_projection_normalization
    (hTensor : ∀ T : Scheme.{u},
      ∃ ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory) ⟶
          Functor.mapHomotopyCategory
            (MonoidalCategory.tensorLeft
            ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
              (Mod.regular (condensedRingObj
                (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) (.up ℤ) ⋙
            DerivedCategory.Qh,
        Functor.IsLeftDerivedFunctor
          (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory)
          ε (HomotopyCategory.quasiIso
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ))) :
    ∃ c : IntegralResiduePullComparisons.{u} ℓ E,
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        ∃ m : (residueExchangeUpperStar (integralCoeff ℓ E) f).Monoidal,
          letI := m
          ∀ K : residueExchangeDerived (integralCoeff ℓ E) X,
            ∃ (s :
                (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategory.obj
                    ((residueExchangeReduction ℓ E Y).obj
                      ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K)) ≅
                  (residueExchangeLowerStar (integralCoeff ℓ E) f).obj K ⊗
                    residueExchangeCoefficient ℓ E Y)
              (e :
                (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategory.obj
                    ((residueExchangeReduction ℓ E X).obj K) ≅
                  K ⊗ (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
                    (residueExchangeCoefficient ℓ E Y)),
              (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategory.map
                  ((c.push f).app K) ≫
                (c.restrictPushIso f).hom.app ((residueExchangeReduction ℓ E X).obj K) ≫
                (residueExchangeLowerStar (integralCoeff ℓ E) f).map e.hom =
                s.hom ≫
                  (((residueExchangeAdjunction (integralCoeff ℓ E) f).rightAdjointProjectionMap
                    (Functor.OplaxMonoidal.δNatTrans
                      (residueExchangeUpperStar (integralCoeff ℓ E) f))).app K).app
                    (residueExchangeCoefficient ℓ E Y)
```

## New

The new signature, verbatim (identical to Old):

```lean
theorem integralResidue_projection_normalization
    (hTensor : ∀ T : Scheme.{u},
      ∃ ε : DerivedCategory.Qh ⋙ (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory) ⟶
          Functor.mapHomotopyCategory
            (MonoidalCategory.tensorLeft
            ((Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).obj
              (Mod.regular (condensedRingObj
                (Profinite.continuousMapRingObj.{u} (integralResidue ℓ E)) T)))) (.up ℤ) ⋙
            DerivedCategory.Qh,
        Functor.IsLeftDerivedFunctor
          (integralReduction ℓ E T ⋙
            (Mod.comap (coefficientMap (integralReductionMap ℓ E) T)).mapDerivedCategory)
          ε (HomotopyCategory.quasiIso
            (Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
              (condensedRingObj (integralCoeff ℓ E) T)) (.up ℤ))) :
    ∃ c : IntegralResiduePullComparisons.{u} ℓ E,
      ∀ {X Y : Scheme.{u}} (f : X ⟶ Y),
        ∃ m : (residueExchangeUpperStar (integralCoeff ℓ E) f).Monoidal,
          letI := m
          ∀ K : residueExchangeDerived (integralCoeff ℓ E) X,
            ∃ (s :
                (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategory.obj
                    ((residueExchangeReduction ℓ E Y).obj
                      ((residueExchangeLowerStar (integralCoeff ℓ E) f).obj K)) ≅
                  (residueExchangeLowerStar (integralCoeff ℓ E) f).obj K ⊗
                    residueExchangeCoefficient ℓ E Y)
              (e :
                (Mod.comap (coefficientMap (integralReductionMap ℓ E) X)).mapDerivedCategory.obj
                    ((residueExchangeReduction ℓ E X).obj K) ≅
                  K ⊗ (residueExchangeUpperStar (integralCoeff ℓ E) f).obj
                    (residueExchangeCoefficient ℓ E Y)),
              (Mod.comap (coefficientMap (integralReductionMap ℓ E) Y)).mapDerivedCategory.map
                  ((c.push f).app K) ≫
                (c.restrictPushIso f).hom.app ((residueExchangeReduction ℓ E X).obj K) ≫
                (residueExchangeLowerStar (integralCoeff ℓ E) f).map e.hom =
                s.hom ≫
                  (((residueExchangeAdjunction (integralCoeff ℓ E) f).rightAdjointProjectionMap
                    (Functor.OplaxMonoidal.δNatTrans
                      (residueExchangeUpperStar (integralCoeff ℓ E) f))).app K).app
                    (residueExchangeCoefficient ℓ E Y)
```

Added public import and local instance selection:

```lean
public import Sheaf.Paper.IntegralResidueDerivedMonoidal
attribute [local instance 2000] residueExchangeIntegralDerivedMonoidal
```

The new API defines the named instance by the existing instance:

```lean
@[instance_reducible] noncomputable def residueExchangeIntegralDerivedMonoidal (T : Scheme.{u}) :
    MonoidalCategory (residueExchangeDerived (integralCoeff ℓ E) T) :=
  inferInstance
```

Three private categorical helpers prove the double-mate and normalization
identities. None appears in a public signature or public definition. No target
statement, binder, universe, existing definition body, or declaration visibility
changes. The new instance is used only locally; it is not registered globally.
All tensor products and projection maps are definitionally the existing ones.
Consequently no target acquires a changed meaning from this local naming.

## Users

`tools/downstream.py Sheaf.Paper.IntegralResidueProjectionNormalization --uses integralResidue_projection_normalization`
lists only the direct consumer and the item as name users; the full downstream
closure is included below. No consumer needs adaptation. The existing direct
consumer compiled unchanged against the delivered overlay after the instance was
marked instance_reducible.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.IntegralResidueProjectionNormalization | D3 | Local proof and instance naming only. |
| Sheaf.Paper.BoundedExchangeAmbient | unclaimed | Transitive consumer; no declaration or instance registration changes. |
| Sheaf.Paper.IntegralExchangeReduction | unclaimed | Transitive consumer; no declaration or instance registration changes. |
| Sheaf.Paper.IntegralFiniteExchangeComparison | unclaimed | Transitive consumer; no declaration or instance registration changes. |
| Sheaf.Paper.IntegralResidueComparisons | unclaimed | Calls unchanged theorem; compiled unchanged against overlay. |
| Sheaf.Paper.IntegralResidueExchange | unclaimed | Transitive consumer; no declaration or instance registration changes. |
| Sheaf.Paper.IntegralResidueExchangeAlgebra | unclaimed | Transitive consumer; no declaration or instance registration changes. |
| Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.ProperApp | unclaimed | Transitive consumer; no declaration or instance registration changes. |
| TargetsCheck | unclaimed | Transitive consumer; no declaration or instance registration changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.CompactSupport | unclaimed | Transitive consumer; no declaration or instance registration changes. |
| WeilConjectures.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.Proper | unclaimed | Transitive consumer; no declaration or instance registration changes. |

## Status

landed 20261016T101204-L-2230257 2026-10-16 (merge of deliver/D3/Sheaf.Paper.IntegralResidueProjectionNormalization)
