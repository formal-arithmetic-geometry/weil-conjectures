# closed_inverseImage_preserves_limits proof-local localization helpers

## Reason

Proving canonical evaluation requires continuity of the two composites of site functors
in a weakly etale localization square. These instances are private, in the proof's
localization section. Preflight classified the earlier anonymous local instances as an
interface change. Both are now named private instances; all new functions and lemmas
are private and are used only in the proof. The main theorem and lift definition keep
identical signatures, universes and visibility. No public import is added or removed.

## Old

No local continuity declarations in this module; the main theorem's proof was `by sorry`.

## New

```lean
private instance localPullbackMapContinuous :
    (MorphismProperty.Over.pullback @WeaklyEtale ⊤ g' ⋙
      MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j')).IsContinuous
        (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')
private instance localMapPullbackContinuous :
    (MorphismProperty.Over.map ⊤ (inferInstance : @WeaklyEtale _ _ j) ⋙
      MorphismProperty.Over.pullback @WeaklyEtale ⊤ g'').IsContinuous
        (Scheme.ProEt.topology U) (Scheme.ProEt.topology Z')
```

Both proofs compose the existing continuous base-change and localization functors.
Section variables, opens, and these private instances only support the private helpers.
No consumer uses these names, and no existing exported declaration changes meaning.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits | D7 | Private proof helpers only; original public signatures and definitions unchanged. |

No public signature or definition changed, so no consumer adaptation or target review
is necessary. No other group's module is edited.

## Status

landed 20261019T002525-L-2147500 2026-10-19 (merge of deliver/D7/Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits)
