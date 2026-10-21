# AlgebraicGeometry.perfectOverlapTailProjectionComponent

## Reason

The assigned rework row records a failed cluster restoration. The current shared
source already contains N2's repair and its complete zero-hole proof compiles
before this delivery (20.5 seconds). Do not claim that repair or a hole closure
again. Reduce the proof's dependency surface instead: establish the geometric
projection equations directly on the raw cartesian isomorphisms, using Mathlib,
and reuse the core transport API's existing local-composition equation.

## Old

The projection proof block, verbatim:

```lean
    have ht : eX.inv ≫ t = pullback.fst s b ≫ a := by
      simpa only [perfectOverlapStageSchemeIso_eq_raw, eX, eY, t, jX, iX,
        W, s, a, Scheme.Hom.preimage_inf] using
        perfectOverlapStageSchemeIso_inv_projection g pX pY b hg U V L hWL
    have hp : eF.inv ≫ p = pullback.fst s q ≫ a := by
      simpa only [perfectOverlapStageSchemeIso_eq_raw, eF, p, jK, iK,
        W, s, a, Scheme.Hom.preimage_inf] using
        perfectOverlapStageSchemeIso_inv_projection f pK pY q hf U V L hWL
```

The proof also imports `Sheaf.AlgebraicGeometry.PerfectOverlapStageSchemeIso`
and `Sheaf.AlgebraicGeometry.PerfectOverlapRestrictedComposition`, and applies
`perfectOverlapCompositeLocalIso_eq_compositionTo g gk f hgf L`.

## New

```lean
    have ht : eX.inv ≫ t = pullback.fst s b ≫ a := by
      change eY.inv ≫ (X.homOfLE _ ≫ (g ∣_ L)) = _
      rw [← morphismRestrict_homOfLE g W L hWL, ← Category.assoc]
      exact congrArg (fun k ↦ k ≫ a)
        (((isPullback_morphismRestrict g W).paste_vert hg).isoPullback_inv_fst)
    have hp : eF.inv ≫ p = pullback.fst s q ≫ a := by
      change eK.inv ≫ (K.homOfLE _ ≫ (f ∣_ L)) = _
      rw [← morphismRestrict_homOfLE f W L hWL, ← Category.assoc]
      exact congrArg (fun k ↦ k ≫ a)
        (((isPullback_morphismRestrict f W).paste_vert hf).isoPullback_inv_fst)
```

Apply `perfectOverlapCompositeLocalIso_eq_compositionTo_global g gk f hgf L`,
already exported by the public composite-stage-tail dependency. Remove both
superseded proof imports. Remove the redundant direct proof imports of
`Sheaf.AlgebraicGeometry.PerfectOverlapNestedPullbackSquare` and
`Sheaf.AlgebraicGeometry.PerfectOverlapStageEquivalence`: their declarations are
already public dependencies of the composite-stage-tail interface.

The theorem's exact signature, visibility, and both public imports are unchanged.
No definition is changed and no new declaration is introduced. Update the theorem's
proof explanation and the existing node's proof and proof_origin to match these
local replacements; its statement, attachments and dependencies are preserved.

## Users

The source-only downstream query reports zero current importers. The quarantined
parent still uses this theorem, and its call was checked against the unchanged
signature. Zero live importers is not treated as permission to withdraw anything.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent | E2 | Direct projection proof and reduced proof imports; zero holes. |
| Sheaf.AlgebraicGeometry.PerfectOverlapProjectionCompositionComponent | quarantined; not adapted | Its existing theorem application has the same type and arguments. |

The unit realization route is unchanged. No consumer adaptation or target semantic
review is required, because no public declaration or mathematical construction changes.

## Status

landed 20261021T233640-L-843316 2026-10-21 (merge of deliver/E2/Sheaf.AlgebraicGeometry.PerfectOverlapTailProjectionComponent)
