# compactificationRefinementComponent

## Reason

Delivery path: `coord/changes/A4-canonical-refinement-transport.md`.
This record is included directly in the delivery at that repository-relative path.
The returned head `a0dcd30cf28` passed mathematical review, but its landing rejected a
reviewer fix named only `A4-canonical-refinement-transport.md`. Any further reviewer
edit to this record must identify its full repository-relative path above.

The functor equality `eqToIso (congrArg ... h.hom.hom.hom_g)` forces the kernel to
repeatedly reduce the derived functors and their localized Hom types. The original
component invertibility proof reaches a deterministic kernel timeout; the profiler
records repeated `ShrinkHoms` conversions at this transport. Derive the canonical
underived `lowerStarCongr` isomorphism instead. Equality induction proves that its
hom is exactly the former `eqToIso` hom (`derive_eqToIso` in the delivered module).
The isolated component-invertibility check changes from a kernel timeout after
35 seconds to a successful compile in 6.8 seconds.

## Old

```lean
def compactificationRefinementComponent {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (h : d ⟶ c)
    (K : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⟶
      (rightDerivedLowerShriekOfCompactification Λ d.obj.obj).obj K :=
  (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map (localizingRefinementMap Λ h K) ≫
    (refinementDerivedLowerStarComp Λ h.hom.hom.hom c.obj.obj.g).inv.app
      ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K) ≫
    (eqToIso (congrArg (fun g ↦ (lowerStar Λ g).rightDerivedFunctor)
      h.hom.hom.hom_g)).hom.app
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K)
```

## New

```lean
def compactificationRefinementComponent {X Y : Scheme.{u}} {f : X ⟶ Y}
    {c d : Compactification.BoundaryCompactification f} (h : d ⟶ c)
    (K : DerivedCategory
      (CategoryTheory.Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :
    (rightDerivedLowerShriekOfCompactification Λ c.obj.obj).obj K ⟶
      (rightDerivedLowerShriekOfCompactification Λ d.obj.obj).obj K :=
  (lowerStar Λ c.obj.obj.g).rightDerivedFunctor.map (localizingRefinementMap Λ h K) ≫
    (refinementDerivedLowerStarComp Λ h.hom.hom.hom c.obj.obj.g).inv.app
      ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K) ≫
    (Functor.rightDerivedFunctorNatIso (lowerStarCongr Λ h.hom.hom.hom_g)).hom.app
        ((openImmersionLowerShriek Λ d.obj.obj.i).mapDerivedCategory.obj K)
```

The module publicly imports `ModuleObject.UpperLowerStar.Coherence` for the canonical
underived congruence. Its signature is unchanged verbatim. This changes only a
canonical equality transport to its provably equal derived form. No hypothesis, object,
coefficient structure, normalization or conclusion changes.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicProperLocalizingAdjunctionComparison | unclaimed | Compiled unchanged against the delivered main module. |
| Sheaf.Paper.BrownExceptionalAdjoint | unclaimed | Compiled unchanged against the delivered main module (reviewer check, 2026-10-25). |
| Sheaf.Paper.CompactificationCoherenceCocycle | A4 | Main proof compiled in 22.5 seconds. |
| Sheaf.Paper.CompactificationRefinementIdentity | unclaimed | Adapted only by unfolding and existing derived-congruence equality; compiles. |
| Sheaf.Paper.IntegralDirectImageTower | unclaimed | Compiled unchanged against the delivered main module. |
| Sheaf.Paper.LocalizingLowerShriekComposition | unclaimed | Compiled unchanged against the delivered main module. |
| Sheaf.Paper.NonrationalLocalizingLowerShriekComposition | unclaimed | Compiled unchanged against the delivered main module. |
| Sheaf.SixFunctors.ScalarSixCompactSupport | unclaimed | Compiled unchanged against the delivered main module; signatures and refinement morphisms retain their meaning. |

These are all eight modules listed by the current `tools/downstream.py --uses
compactificationRefinementComponent` (BrownExceptionalAdjoint added by the reviewer). No other module is changed unless its proof must
be adapted to this equal transport. The definition is in the targets' closure, so its
meaning is reopened for independent review; the equality-induction proof certifies the
same morphism rather than merely some isomorphism.

## Status

landed 20261025T050713-L-3833998 2026-10-25 (merge of deliver/A4/Sheaf.Paper.CompactificationCoherenceCocycle)
