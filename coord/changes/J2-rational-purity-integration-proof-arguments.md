# WeilConjectures.RationalSmoothPurityCanonical.finiteIntegration

## Reason

The original unchanged item compiled in 94 seconds, exceeding the 60-second limit.
The declaration profiler located roughly 9.4 seconds in elaborating the first
`inferInstanceAs` argument of `diagonalDualizingObject`. Bind its six existing
proposition-valued typeclass arguments before constructing the categorical
composite. This keeps their types independent of unresolved metavariables in the
large composite. The resulting definition is definitionally equal to the original
by proof irrelevance; every functor, orientation, comparison, counit, and their order
is identical. Local priorities for the canonical derived and scalar-localization
category instances also avoid elaboration through competing category presentations.
These priorities affect their files only. No target or public type changes.
After those improvements the full module still took 74 seconds. Under the explicit
worker prompt step 3a, extract the self-contained finite setup into
`Sheaf.Paper.RationalSmoothPurityFiniteTrace` and publicly re-export it from the item.
The 14 extracted public declarations keep their full names, signatures, bodies
(except the proof-argument caching above), and attributes. No declarations disappear
from the imported API. The DAG attachment moves to
`def-pur-canonical-finite-trace-setup`; its proof creates no holes. The independent ordinary monoidal presentation and its private tensor-comparison
proof move into the same setup module; the item retains the local irreducibility
setting and imports the private theorem only for proof use. The item retains
its five remaining holes. The added module defines no alternative purity map.

## Old

```lean
def finiteIntegration (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) c).obj
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
          ((AdicSmoothDualizing.levelSetting P n).diagonalTwist X d)) ⟶
      (AdicSmoothDualizing.levelSetting P n).coefficientUnit Y := by
  letI : HasCompactification f := c.hasCompactification
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek f
    (AdicSmoothDualizing.levelSetting P n).Coefficient
  refine (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n c).hom.app _ ≫ ?_
  refine (ProEtale.sfIntrinsicCompactSupportComparison
      (AdicSmoothDualizing.levelSetting P n).Ring c).hom.app _ ≫ ?_
  exact (sfIntrinsicDerivedEquivalence Y (AdicSmoothDualizing.levelSetting P n).Ring).functor.map
      ((ProEtale.sfFixedCompactSupport
        (AdicSmoothDualizing.levelSetting P n).Ring c).map
        ((@PurityFiniteSetting.diagonalDualizingObject
          (AdicSmoothDualizing.levelSetting P n) X Y d f
          (inferInstanceAs (IsSeparated f)) (inferInstanceAs (LocallyOfFiniteType f))
          (inferInstanceAs (QuasiCompact f)) (inferInstanceAs (SmoothOfRelativeDimension d f))
          (Y ↘ Spec (.of P.field.k))
          (inferInstanceAs (LocallyOfFiniteType (Y ↘ Spec (.of P.field.k))))
          (inferInstanceAs (QuasiCompact (Y ↘ Spec (.of P.field.k))))).inv ≫
          ((AdicSmoothDualizing.levelSetting P n).diagonalDualizingComparison f).hom) ≫
        (ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient) c).hom.app
            ⟨_, finiteDualizingPlus P f c n d⟩ ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
          Y).mapDerivedCategory.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso
              (AdicSmoothDualizing.levelSetting P n).Coefficient c
              (HasCompactification.compactification f)).hom.app
                ⟨_, finiteDualizingPlus P f c n d⟩ ≫
              (Etale.rightDerivedUpperShriekAdjunction
                (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
                f).counit.app _))
```

## New

The finite setup declarations listed by the new node now reside in
`lean/Sheaf/Paper/RationalSmoothPurityFiniteTrace.lean`; the item adds
`public import Sheaf.Paper.RationalSmoothPurityFiniteTrace`. Existing public imports
remain verbatim. The three strict-augmentation proof imports move with that proof.


```lean
def finiteIntegration (n d : ℕ) [SmoothOfRelativeDimension d f] :
    (PurCompactSupport.image (PurCompactSupport.finite P.coefficients.l P.extension
      (n + 1) (Nat.succ_pos n)) c).obj
        ((sfIntrinsicDerivedEquivalence X
          (Padic.coefficientExtensionRing P.coefficients.l P.extension (n + 1))).functor.obj
          ((AdicSmoothDualizing.levelSetting P n).diagonalTwist X d)) ⟶
      (AdicSmoothDualizing.levelSetting P n).coefficientUnit Y := by
  let hfSep : IsSeparated f := inferInstance
  let hfType : LocallyOfFiniteType f := inferInstance
  let hfQc : QuasiCompact f := inferInstance
  let hfSmooth : SmoothOfRelativeDimension d f := inferInstance
  let hYType : LocallyOfFiniteType (Y ↘ Spec (.of P.field.k)) := inferInstance
  let hYQc : QuasiCompact (Y ↘ Spec (.of P.field.k)) := inferInstance
  letI : HasCompactification f := c.hasCompactification
  letI := Etale.isLeftAdjoint_rightDerivedLowerShriek f
    (AdicSmoothDualizing.levelSetting P n).Coefficient
  refine (PurCompactSupport.finiteImageIso P.coefficients.l P.extension n c).hom.app _ ≫ ?_
  refine (ProEtale.sfIntrinsicCompactSupportComparison
      (AdicSmoothDualizing.levelSetting P n).Ring c).hom.app _ ≫ ?_
  exact (sfIntrinsicDerivedEquivalence Y (AdicSmoothDualizing.levelSetting P n).Ring).functor.map
      ((ProEtale.sfFixedCompactSupport
        (AdicSmoothDualizing.levelSetting P n).Ring c).map
        ((@PurityFiniteSetting.diagonalDualizingObject
          (AdicSmoothDualizing.levelSetting P n) X Y d f
          hfSep hfType
          hfQc hfSmooth
          (Y ↘ Spec (.of P.field.k))
          hYType
          hYQc).inv ≫
          ((AdicSmoothDualizing.levelSetting P n).diagonalDualizingComparison f).hom) ≫
        (ProEtale.rightDerivedLowerShriekOfCompactificationComparisonIso
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient) c).hom.app
            ⟨_, finiteDualizingPlus P f c n d⟩ ≫
        (ProEtale.comparisonUpperStar
          (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
          Y).mapDerivedCategory.map
            ((Etale.rightDerivedLowerShriekOfCompactificationPlusιIso
              (AdicSmoothDualizing.levelSetting P n).Coefficient c
              (HasCompactification.compactification f)).hom.app
                ⟨_, finiteDualizingPlus P f c n d⟩ ≫
              (Etale.rightDerivedUpperShriekAdjunction
                (ModuleCat.{u + 1} (AdicSmoothDualizing.levelSetting P n).Coefficient)
                f).counit.app _))
```

## Users

All direct importers retain the same public declarations, types, attributes,
and definitionally equal constructions. No consumer edits are required. The
normal delivery checks compile these importers against the delivered file.
The holder column describes the shared snapshot; the delivery tool reads current
claims on its fetched base.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantPurityFrobeniusSquare | unclaimed | Same definition by proof irrelevance; no adaptation. |
| Sheaf.Paper.NormalizedFieldPurityTraceData | unclaimed | Same definition by proof irrelevance; no adaptation. |
| Sheaf.Paper.NormalizedOrientationPerfectDuality | unclaimed | Same definition by proof irrelevance; no adaptation. |
| Sheaf.Paper.PurityOrientationDatum | unclaimed | Same definition by proof irrelevance; no adaptation. |
| Sheaf.Paper.RationalWeilPurityNaturalityMate | unclaimed | Same definition by proof irrelevance; no adaptation. |
| Sheaf.Paper.SmoothExchangeScalarCompatibility | F4 | Same definition by proof irrelevance; no adaptation. |
| Sheaf.Paper.SmoothOrientationCoefficientFamily | unclaimed | Same definition by proof irrelevance; no adaptation. |
| Sheaf.Paper.SmoothOrientedExchangeComparisons | unclaimed | Same definition by proof irrelevance; no adaptation. |
| Sheaf.Paper.TowerTracePurityComparisonData | unclaimed | Same definition by proof irrelevance; no adaptation. |
| Sheaf.Paper.WeilPurityEquivarianceData | unclaimed | Same definition by proof irrelevance; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityLineComparisons | unclaimed | Same definition by proof irrelevance; no adaptation. |
| Sheaf.SecSmoothPurity.RationalPurityTraceCoherence | unclaimed | Same definition by proof irrelevance; no adaptation. |
| Sheaf.UpstreamExtra.WeilConjectures.WeilSheaf.LowerShriekFunctoriality | unclaimed | Same definition by proof irrelevance; no adaptation. |

| Sheaf.Paper.RationalSmoothPurityCanonical | J2 | Uses the extracted finite setup and private tensor comparison with identical types. |

## Status

landed 20261028T020515-L-2518146 2026-10-28 (merge of deliver/J2/Sheaf.Paper.RationalSmoothPurityCanonical)
