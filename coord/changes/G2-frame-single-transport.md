# frameClassOnPullback

## Reason

Name the ordinary functorial transport before specializing it to the derived category. This avoids repeated expansion of the localization in class-transport proofs. The canonical coefficient isomorphism and concrete class are exactly the same.

## Old

```lean
def frameClassOnPullback (P : PurityFiniteSetting.{u}) {B V Z : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension P.level v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)] (c : ℕ)
    (hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞)) (F : i.EtaleFrame c) :
    cupSupportedHom P (pullback.snd i F.e)
      ((cupSingle P F.U).obj (P.frameTwist F.U c)) (2 * (c : ℤ)) :=
  (cupSingle P F.U).map
    (P.frameClosedCoefficientIso (F.U.zeroLocusSubschemeι (Set.range F.f))
      (pullback.snd i F.e) F.isPullback.isoPullback F.isPullback.isoPullback_hom_snd).inv ≫
    P.frameClass b v i c hcodim F
```

## New

```lean
def frameClassOnPullback (P : PurityFiniteSetting.{u}) {B V Z : Scheme.{u}}
    (b : B ⟶ Spec (.of P.field.k)) (v : V ⟶ B)
    [SmoothOfRelativeDimension P.level v] (i : Z ⟶ V) [IsClosedImmersion i]
    [Smooth (i ≫ v)] (c : ℕ)
    (hcodim : ∀ z : Z, ringKrullDim (V.presheaf.stalk (i z)) =
      ringKrullDim (Z.presheaf.stalk z) + (c : WithBot ℕ∞)) (F : i.EtaleFrame c) :
    cupSupportedHom P (pullback.snd i F.e)
      ((cupSingle P F.U).obj (P.frameTwist F.U c)) (2 * (c : ℤ)) :=
  let _codimension := hcodim
  P.frameProductOnSupport (pullback.snd i F.e) (F.e ≫ v ≫ b) c F.f
    F.isPullback.isoPullback F.isPullback.isoPullback_hom_snd
```

The new `frameProductOnSupport` transports exactly the same `frameBoundaryProduct` through `frameSingleTransport S q α := S.map q.inv ≫ α`. The old `frameClass` is that same boundary product. Unfolding these names gives the old body verbatim. The unused local `_codimension` records the unchanged argument without changing the value. Public statement signatures stay identical.

## Users

`tools/downstream.py Sheaf.Paper.PurityFrameIndependence --uses frameClassOnPullback` lists only the item itself as a direct declaration user. All downstream modules are listed below.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.PurityFrameIndependence | G2 | Proof filled using the same class transport. |
| Sheaf.Paper.CartierClassAgreement | B7 | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.CartierRelativeBoundaryRealization | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.CartierRelativeKummerRealization | B8 | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.ChernFlagFormula | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.FlagLocalComparison | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.FlagPullbackInjective | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.LineZeroClassEtaleRealization | S8 | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.LocalizedFlagProduct | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.LocalizedTopChern | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.ProjectiveBundleFormula | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.PurityChernClasses | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.PurityDivisorClass | S3 | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.RegularImmersionCancellation | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.RegularImmersionClassData | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.RegularImmersionExteriorClass | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.RegularImmersionPurity | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.RegularImmersionSignedEvaluation | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.SupportedProjectionSplitting | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.VectorBundleThom | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.VectorBundleThomClass | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.VectorBundleThomMaps | unclaimed | Definitionally identical transport; no adaptation. |
| Sheaf.Paper.VectorBundleThomProduct | unclaimed | Definitionally identical transport; no adaptation. |

No target meaning changes: the new body is definitionally the old composition.

## Status

landed 20261025T041157-L-1052777 2026-10-25 (merge of deliver/G2/Sheaf.Paper.PurityFrameIndependence)
