# adicProjection and the integral shift/trace definitions

## Reason

The completed-projection, trace-tensor, and arbitrary-adjunction-transpose steps need
these existing definitions without importing their parent theorem. Move the definitions
verbatim into AdicProjectionShiftData and publicly import that module from the old owner.
This avoids an import cycle. No signature, body, attribute, instance or target meaning changes.

## Old

In lean/Sheaf/Paper/AdicProjectionShiftCoherence.lean:

```lean
/-- Use the recorded triangulated closure with an explicit coefficient-field package.
This exposes its inherited shift on the unbundled finite-Tor category as well.
Source: blueprint integral finite-Tor convention
(blueprint: lem-pur-adic-projection-shift-coherence). -/
instance adicFiniteTorTriangulated (W : Scheme.{u}) :
    (finiteTorConstructibleIntegral l E W).IsTriangulated :=
  ConstructibleExceptionalCoefficients.integralTriangulated l { carrier := E } W

/-- The canonical projection in completed coordinates: inverse source completion,
the proper/open projection of def-exchange-projection, then target completion.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence). -/
def adicProjection {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : RingedModels l E) (b : RingedOpenComparisons l E d) (c : Compactification f)
    (T : Integral l E X) (K : Integral l E Y)
    (h : IsIso (((d.tensor Y).chi l E).app
      ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T, K))) :
    (integralCompletedTensor l E Y).obj
        ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T, K) ⟶
      (PurCompactSupport.image (PurCompactSupport.completed l E) c).obj
        ((integralCompletedTensor l E X).obj (T, (integralDerivedPullback l E f).obj K)) :=
  @inv _ _ _ _ (((d.tensor Y).chi l E).app
      ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T, K)) h ≫
    ringedCompactificationProjection l E d b c T K ≫
    (PurCompactSupport.image (PurCompactSupport.completed l E) c).map
      ((d.tensor X).ordinary.tensor.map
        (Prod.mkHom (𝟙 T) (((d.pull f).unit l E).app K)) ≫
          ((d.tensor X).chi l E).app (T, (integralDerivedPullback l E f).obj K))

/-- The map t tensor 1 followed by the canonical coefficient-unit identification.
It is written through ordinary tensor and its actual completion unit, so no second
choice of completed unitors is introduced.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence). -/
def adicTraceTensor {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : RingedModels l E) (c : Compactification f)
    (T : Integral l E X) (K : Integral l E Y)
    (h : IsIso (((d.tensor Y).chi l E).app
      ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T, K)))
    (t : (PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T ⟶
      (calculus l E Y).integralClosed.monoidal.tensorUnit) :
    (integralCompletedTensor l E Y).obj
      ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T, K) ⟶ K :=
  @inv _ _ _ _ (((d.tensor Y).chi l E).app
      ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T, K)) h ≫
    (d.tensor Y).ordinary.tensor.map (Prod.mkHom t (𝟙 K)) ≫
    eqToHom (congrArg (fun F ↦ F.obj
      ((calculus l E Y).integralClosed.monoidal.tensorUnit, K)) (d.tensorClosed Y)) ≫
    ((calculus l E Y).integralClosed.monoidal.leftUnitor K).hom

/-- The displayed u_K, using the inverse of the specified projection, not an arbitrary
isomorphism between its endpoints.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence). -/
def adicTraceMap {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : RingedModels l E) (b : RingedOpenComparisons l E d) (c : Compactification f)
    (T : Integral l E X) (K : Integral l E Y)
    (h : IsIso (((d.tensor Y).chi l E).app
      ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T, K)))
    (hp : IsIso (adicProjection l E d b c T K h))
    (t : (PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T ⟶
      (calculus l E Y).integralClosed.monoidal.tensorUnit) :=
  @inv _ _ _ _ (adicProjection l E d b c T K h) hp ≫ adicTraceTensor l E d c T K h t

/-- Move K[1] through completed pullback and the second tensor slot. The latter
comparison has coefficient (-1)^a on a tensor summand of first degree a.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence). -/
def adicTensorPullShift {X Y : Scheme.{u}} (f : X ⟶ Y)
    (T : Integral l E X) (K : Integral l E Y) :
    (integralCompletedTensor l E X).obj (T, (integralDerivedPullback l E f).obj (K⟦(1 : ℤ)⟧)) ≅
      ((integralCompletedTensor l E X).obj (T, (integralDerivedPullback l E f).obj K))⟦(1 : ℤ)⟧ :=
  (integralCompletedTensor l E X).mapIso
      (Iso.prod (Iso.refl T) (((integralDerivedPullback l E f).commShiftIso (1 : ℤ)).app K)) ≪≫
    ((tensorShifts l E).integralRight X 1).app (T, (integralDerivedPullback l E f).obj K)

/-- The canonical fully faithful inclusion comparison is retained explicitly;
shifts in a full subcategory need not be definitionally equal to ambient shifts.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence). -/
def adicInputShift (W : Scheme.{u})
    (K : finiteTorConstructibleIntegralCategory l E W) :
    (K⟦(1 : ℤ)⟧).obj ≅ K.obj⟦(1 : ℤ)⟧ :=
  ((finiteTorConstructibleIntegral l E W).ι.commShiftIso (1 : ℤ)).app K

/-- The second-variable comparison, including the full-subcategory inclusion.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence). -/
def adicTensorInputShift {X Y : Scheme.{u}} (f : X ⟶ Y) (T : Integral l E X)
    (K : finiteTorConstructibleIntegralCategory l E Y) :
    (integralCompletedTensor l E X).obj
        (T, (integralDerivedPullback l E f).obj (K⟦(1 : ℤ)⟧).obj) ≅
      ((integralCompletedTensor l E X).obj
        (T, (integralDerivedPullback l E f).obj K.obj))⟦(1 : ℤ)⟧ :=
  (integralCompletedTensor l E X).mapIso
      (Iso.prod (Iso.refl T)
        ((integralDerivedPullback l E f).mapIso (adicInputShift l E Y K))) ≪≫
    adicTensorPullShift l E f T K.obj

/-- The projection shift square, including invertibility of the source completion.
This same equation is used below for the proper-only and open-only constituents.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence). -/
def AdicProjectionShiftSquare {X Y : Scheme.{u}} {f : X ⟶ Y}
    (d : RingedModels l E) (b : RingedOpenComparisons l E d) (c : Compactification f)
    (T : finiteTorConstructibleIntegralCategory l E X) : Prop :=
  ∃ hχ : ∀ K : finiteTorConstructibleIntegralCategory l E Y,
      IsIso (((d.tensor Y).chi l E).app
        ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T.obj, K.obj)),
    ∀ K : finiteTorConstructibleIntegralCategory l E Y,
      adicProjection l E d b c T.obj (K⟦(1 : ℤ)⟧).obj (hχ (K⟦(1 : ℤ)⟧)) ≫
          (PurCompactSupport.image (PurCompactSupport.completed l E) c).map
            (adicTensorInputShift l E f T.obj K).hom ≫
          ((PurCompactSupport.image (PurCompactSupport.completed l E) c).commShiftIso
            (1 : ℤ)).hom.app _ =
        (integralCompletedTensor l E Y).map
            (Prod.mkHom (𝟙 _) (adicInputShift l E Y K).hom) ≫
          ((tensorShifts l E).integralRight Y 1).hom.app
            ((PurCompactSupport.image (PurCompactSupport.completed l E) c).obj T.obj, K.obj) ≫
          (adicProjection l E d b c T.obj K.obj (hχ K))⟦(1 : ℤ)⟧'

section Exceptional
variable (D : FiniteFieldDatum.{u}) (C : D.CoefficientDatum)
  (F : Type u) [Field F] [Algebra ℚ_[C.l] F] [FiniteDimensional ℚ_[C.l] F]
  {X Y : Scheme.{u}}
  [X.Over (Spec (.of D.k))] [Y.Over (Spec (.of D.k))]
  [LocallyOfFiniteType (X ↘ Spec (.of D.k))] [QuasiCompact (X ↘ Spec (.of D.k))]
  [IsSeparated (X ↘ Spec (.of D.k))]
  [LocallyOfFiniteType (Y ↘ Spec (.of D.k))] [QuasiCompact (Y ↘ Spec (.of D.k))]
  [IsSeparated (Y ↘ Spec (.of D.k))]
  (f : X ⟶ Y) [f.IsOver (Spec (.of D.k))]
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]
  (S : ConstructibleExceptionalCoefficients.RingSystem C.l C.Qbar D C.different (f := f))
  (c : Compactification f)

/-- The left shift transported from exact open extension and proper derived image
through their specified fully faithful realization.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence). -/
@[instance_reducible]
def adicSupportShift :
    (S.operation c (.integral { carrier := F })).F.CommShift ℤ :=
  letI : (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).CommShift ℤ :=
    (integralShifts C.l F).compactSupport f c
  letI : ((finiteTorConstructibleIntegral C.l F X).ι).CommShift ℤ := inferInstance
  Functor.CommShift.ofComp
    (F := (S.operation c (.integral { carrier := F })).F)
    (G := (finiteTorConstructibleIntegral C.l F Y).ι)
    (S.left c (.integral { carrier := F })) ℤ

/-- The right-adjoint shift obtained from the canonical compact-support shift.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence). -/
def adicExceptionalShift :
    shiftFunctor (finiteTorConstructibleIntegralCategory C.l F Y) (1 : ℤ) ⋙
        (S.operation c (.integral { carrier := F })).G ≅
      (S.operation c (.integral { carrier := F })).G ⋙
        shiftFunctor (finiteTorConstructibleIntegralCategory C.l F X) (1 : ℤ) :=
  letI := adicSupportShift D C F f S c
  letI := (S.operation c (.integral { carrier := F })).adjunction.rightAdjointCommShift ℤ
  Functor.commShiftIso _ (1 : ℤ)

/-- The ambient arrow of the actual exceptional-adjunction transpose. The left
realization identifies F(A) with precisely Rf_! A before taking the Hom transpose.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence). -/
def adicTranspose
    (A : finiteTorConstructibleIntegralCategory C.l F X)
    (K : finiteTorConstructibleIntegralCategory C.l F Y)
    (v : (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).obj A.obj ⟶ K.obj) :
    A.obj ⟶ ((S.operation c (.integral { carrier := F })).G.obj K).obj :=
  ((S.operation c (.integral { carrier := F })).adjunction.homEquiv A K
    (ObjectProperty.homMk ((S.left c (.integral { carrier := F })).hom.app A ≫ v))).hom

```

## New

Exactly the same declarations, verbatim, in
lean/Sheaf/Paper/AdicProjectionShiftData.lean. The original module begins with:

```lean
public import Sheaf.Paper.AdicProjectionShiftData
```

The definition owner node's lean attachment follows the declarations. The theorem node
retains its theorem attachment. The new data module retains every original public import.
Only unused private proof imports are removed. The original import path continues to expose
the same complete public interface.

## Users

`tools/downstream.py Sheaf.Paper.AdicProjectionShiftCoherence --uses adicProjection`
reports these seven downstream modules. No source-library module is edited.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.AdicTraceTransposeCoefficientCalculus | unclaimed | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.AdicTraceTransposeData | unclaimed | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceConstruction | unclaimed | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceReductionData | unclaimed | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceScalarData | unclaimed | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTensorCoordinates | unclaimed | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.AdicUnitTraceTransposeReductions | unclaimed | Identical definitions publicly re-exported; no adaptation. |
| Sheaf.Paper.AdicProjectionShiftCoherence | W9 | Re-exports unchanged definitions; theorem uses the extracted steps. |
| Sheaf.Paper.AdicCompletedProjectionShift | new in this delivery | Uses the published definitions from their new owner. |
| Sheaf.Paper.AdicTraceTensorShift | new in this delivery | Uses the published definitions from their new owner. |
| Sheaf.Paper.AdicExceptionalShiftCoherence | new in this delivery | Uses the published definitions from their new owner. |

## Status

landed 20261025T101823-L-3740839 2026-10-25 (merge of deliver/W9/Sheaf.Paper.AdicProjectionShiftCoherence)
