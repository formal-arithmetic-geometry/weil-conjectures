/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NH
-/
module

public import Sheaf.Paper.PurityFiniteSetting
public import Sheaf.NumberTheory.Padics.CoefficientExtensionFinite
public import Sheaf.Paper.SfIntegralConstructible
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Sheaf.Paper.ExchangeProjectionSuppliedDomains
public import Sheaf.Paper.CompactSupportProjectionFormula
public import Sheaf.AlgebraicGeometry.ProEtaleIntrinsicExtensionByZero
public import Sheaf.Paper.QcqsCompactSupportRealization
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients
public import Sheaf.SixFunctors.IntegralSystemCanonicalBridge
public import Sheaf.Paper.FiniteTorAmplitudeSites
public import Sheaf.Paper.DerivedPullbackTensorHom
public import Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients
public import Sheaf.SixFunctors.IntegralOperationShiftData
public import Sheaf.SixFunctors.IntegralCompactificationSystemRealization

import Sheaf.Paper.ProjectionMateExact
import Sheaf.AlgebraicGeometry.ProEtaleExtensionZero
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import Sheaf.SixFunctors.IntegralRealizationShiftCoherence

/-! # Shifts of the integral compact-support projection and its trace transpose

Source: blueprint sec-smooth-purity/sk-thm-purity-transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence).

The projection is the proper counit mate followed by the open comparison, transported
by the actual quotient-completion units. All tensors below are the recorded completed
tensors. The first input is arbitrary in the full integral finite-Tor category.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme
namespace WeilConjectures
open IntegralSystemRealization

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

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

/-- The completed projection, the trace map u, and its exceptional transpose commute
with the shift in the second input; the exceptional comparison is uniquely
characterized by the shifted counit. No restriction on the degrees of T is made.
Source: blueprint purity transport, adic Step 2
(blueprint: lem-pur-adic-projection-shift-coherence).

Proof: choose the displayed compactification. Its projection is the canonical proper
counit mate followed by the open tensor comparison (def-exchange-projection), and is
invertible by fix-prop-projection-formula. The ringed projection-mate exactness lemma
gives the shift square of the proper factor. On K-flat representatives of the open
factor, shifting the second tensor input multiplies the summand of first degree a by
(-1)^a on both sides. Exact termwise open extension and pullback composition preserve
this equality. The argument also applies to strict systems over the ring diagram,
before finite evaluation. System projection coherence identifies that map with the
specified proper/open composite. The integral realization maps intertwine this same
map, its whiskerings and the total derived inverse limit. Integral realization shift
coherence transports the system square to the completed map below; it does not infer
an equality from finite evaluations. Invert the projection square and use tensor
naturality for t to obtain the u square. The unique adjunction shift comparison is
characterized by the shifted counit. Transpose the u square through this adjunction
to obtain the gamma square. Apply the same assertion to proper-only and open-only
compactifications to obtain the two constituent squares. -/
theorem adicProjectionShiftCoherence
    (d : RingedModels C.l F) (b : RingedOpenComparisons C.l F d)
    (T : finiteTorConstructibleIntegralCategory C.l F X) :
    ∃ (hχ : ∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        IsIso (((d.tensor Y).chi C.l F).app
          ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).obj T.obj, K.obj)))
      (hA : ∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        finiteTorConstructibleIntegral C.l F X
          ((integralCompletedTensor C.l F X).obj
            (T.obj, (integralDerivedPullback C.l F f).obj K.obj)))
      (hPF : ∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        IsIso (adicProjection C.l F d b c T.obj K.obj (hχ K))),
      (∀ hp : IsProper f,
        AdicProjectionShiftSquare C.l F d b (@Compactification.ofIsProper X Y f hp) T) ∧
      (∀ hj : IsOpenImmersion f,
        AdicProjectionShiftSquare C.l F d b (@Compactification.ofIsOpenImmersion X Y f hj) T) ∧
      (∃! σ : shiftFunctor (finiteTorConstructibleIntegralCategory C.l F Y) (1 : ℤ) ⋙
          (S.operation c (.integral { carrier := F })).G ≅
        (S.operation c (.integral { carrier := F })).G ⋙
          shiftFunctor (finiteTorConstructibleIntegralCategory C.l F X) (1 : ℤ),
        Adjunction.CommShift.CompatibilityCounit
          (S.operation c (.integral { carrier := F })).adjunction
          (Functor.commShiftIso _ (self := adicSupportShift D C F f S c) (1 : ℤ)) σ) ∧
      (∀ K : finiteTorConstructibleIntegralCategory C.l F Y,
        adicProjection C.l F d b c T.obj (K⟦(1 : ℤ)⟧).obj (hχ (K⟦(1 : ℤ)⟧)) ≫
            (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).map
              (adicTensorInputShift C.l F f T.obj K).hom ≫
            ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).commShiftIso
              (1 : ℤ)).hom.app _ =
          (integralCompletedTensor C.l F Y).map
              (Prod.mkHom (𝟙 _) (adicInputShift C.l F Y K).hom) ≫
            ((tensorShifts C.l F).integralRight Y 1).hom.app
              ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).obj T.obj,
                K.obj) ≫
            (adicProjection C.l F d b c T.obj K.obj (hχ K))⟦(1 : ℤ)⟧') ∧
      (∀ (t : (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).obj T.obj ⟶
          (calculus C.l F Y).integralClosed.monoidal.tensorUnit)
        (K : finiteTorConstructibleIntegralCategory C.l F Y),
        adicTraceMap C.l F d b c T.obj (K⟦(1 : ℤ)⟧).obj
            (hχ (K⟦(1 : ℤ)⟧)) (hPF (K⟦(1 : ℤ)⟧)) t ≫
            (adicInputShift C.l F Y K).hom =
          (PurCompactSupport.image (PurCompactSupport.completed C.l F) c).map
              (adicTensorInputShift C.l F f T.obj K).hom ≫
            ((PurCompactSupport.image (PurCompactSupport.completed C.l F) c).commShiftIso
              (1 : ℤ)).hom.app _ ≫
            (adicTraceMap C.l F d b c T.obj K.obj (hχ K) (hPF K) t)⟦(1 : ℤ)⟧' ∧
        adicTranspose D C F f S c
            ⟨_, hA (K⟦(1 : ℤ)⟧)⟩ (K⟦(1 : ℤ)⟧)
            (adicTraceMap C.l F d b c T.obj (K⟦(1 : ℤ)⟧).obj
              (hχ (K⟦(1 : ℤ)⟧)) (hPF (K⟦(1 : ℤ)⟧)) t) ≫
            ((adicExceptionalShift D C F f S c).hom.app K).hom ≫
            (adicInputShift C.l F X
              ((S.operation c (.integral { carrier := F })).G.obj K)).hom =
          (adicTensorInputShift C.l F f T.obj K).hom ≫
            (adicTranspose D C F f S c ⟨_, hA K⟩ K
              (adicTraceMap C.l F d b c T.obj K.obj (hχ K) (hPF K) t))⟦(1 : ℤ)⟧') := by
  sorry

end Exceptional
end WeilConjectures
