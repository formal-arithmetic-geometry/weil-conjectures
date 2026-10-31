/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompletedUnitPullback.CompletedUnitTensorSystemData

/-! # Comparison of the primitive and tensor system inverse images -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory AlgebraicGeometry
attribute [local implicit_reducible] sheafCompose Functor.sheafPushforwardContinuous
  SheafOfModules.pullback SheafOfModules.pullbackPushforwardAdjunction
  WeilConjectures.pullbackTensorSequenceDirect WeilConjectures.PrimitiveCounit.direct
  WeilConjectures.pullbackTensorSequenceInverse WeilConjectures.PrimitiveCounit.inverse
  WeilConjectures.pullbackTensorSequenceDerived WeilConjectures.PrimitiveCounit.pull
  WeilConjectures.pullbackTensorSequenceBase WeilConjectures.PrimitiveCounit.base
  WeilConjectures.CompletedUnitPullback.systemObject
  WeilConjectures.CompletedUnitPullback.systemUnit
namespace WeilConjectures.CompletedUnitPullback

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem ring_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceRing l E f = PrimitiveCounit.ringMap l E f := by
  unfold pullbackTensorSequenceRing pullbackTensorSequenceRingMap
  rfl

private theorem inverse_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceInverse l E f = PrimitiveCounit.inverse l E f := by
  unfold pullbackTensorSequenceInverse PrimitiveCounit.inverse
  unfold pullbackTensorSequenceDirect PrimitiveCounit.direct
  simp only [ring_eq l E f]

/-- The two exact system pullbacks are the same functor.
Source: the component normalization of `pullbackTensorSequenceRing` and Stacks 03D2.
(blueprint: lem-pur-completed-unit-system-pullback-comparison).
Proof: uniqueness of the normalized sequence ring map identifies the direct images.
Both inverse images are the same chosen left adjoint, with proof-irrelevant instances.
Their exact derived functors therefore coincide. -/
theorem systemPullback_eq {X Y : Scheme.{u}} (f : X ⟶ Y) :
    pullbackTensorSequenceDerived l E f = PrimitiveCounit.pull l E f := by
  unfold pullbackTensorSequenceDerived PrimitiveCounit.pull
  simp only [inverse_eq l E f]

/-- The ordinary regular-unit pullback is the primitive multiplication, after the
canonical equality of their system pullbacks.
Source: Stacks 03D2 and 07A4, adjoint of the ring-unit section map.
(blueprint: lem-pur-completed-unit-system-pullback-comparison).
Proof: replace the normalized ring map by its identical primitive components.
The adjunctions then are the same chosen adjunction, so their transposes of the
unit-to-pushforward-unit map coincide. Apply the exact single-complex comparison. -/
theorem systemPullback_regular {X Y : Scheme.{u}} (f : X ⟶ Y) :
    eqToHom (congrArg (fun H ↦ H.obj (systemObject l E Y)) (systemPullback_eq l E f)) ≫
      systemMap l E f = (tensorSystemRegularPullback l E f).hom := by
  apply eq_of_heq
  simp only [eqToHom_comp_heq_iff]
  unfold tensorSystemRegularPullback systemMap systemMultiplication
  simp only [Iso.trans_hom, Functor.mapIso_hom, asIso_hom]
  dsimp only [Iso.app_hom, systemObject, systemUnit, pullbackTensorSequenceBase,
    PrimitiveCounit.base]
  simp only [pullbackTensorSequenceDerived, PrimitiveCounit.pull,
    pullbackTensorSequenceInverse, PrimitiveCounit.inverse,
    pullbackTensorSequenceDirect, PrimitiveCounit.direct,
    SheafOfModules.pullbackObjUnitToUnit, SheafOfModules.pullbackPushforwardAdjunction,
    ]
  have hring := ring_eq l E f
  generalize_proofs
  generalize hφ : pullbackTensorSequenceRing l E f = φ at *
  clear hφ
  subst φ
  rfl

end WeilConjectures.CompletedUnitPullback
