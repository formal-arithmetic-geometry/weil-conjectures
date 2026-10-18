/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NY
-/
module

public import Sheaf.AlgebraicGeometry.LabeledEmbeddedResolution

/-!
# Finite embedded blowup histories

Source: ILO, Expose VIII, 2.3.1, 2.3.4, 2.3.11--2.3.13, pp. 91--94;
Bierstone--Milman--Temkin, Q-universal desingularization, Theorem 6.1 and Addendum,
section 6.3 (blueprint: def-trf-admissible-embedded-history).

The schemes, maps, ideals and comparison isomorphisms are actual data. Smoothness and
reducedness of later stages are not built into a raw history. Admissibility is generated
by maximum-center steps and smooth pullbacks, with precisely the empty stages deleted.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A finite ordinary ambient blowup history of an embedded pair, retaining all center
ideals and the scheme-theoretic strict transforms in chronological order. No regularity
or smoothness conclusion is assumed for later stages.
Source: ILO VIII 2.3.1, 2.3.11 (blueprint: def-trf-admissible-embedded-history). -/
structure EmbeddedResolutionHistory (A : EmbeddedResolutionPair.{u}) (n : ℕ) where
  ambient : (Fin (n + 1))ᵒᵖ ⥤ Scheme.{u}
  intrinsic : (Fin (n + 1))ᵒᵖ ⥤ Scheme.{u}
  inclusion : intrinsic ⟶ ambient
  closed : ∀ j, IsClosedImmersion (inclusion.app (op j))
  initialAmbient : ambient.obj (op 0) ≅ A.P
  initialIntrinsic : intrinsic.obj (op 0) ≅ A.X
  initialInclusion : inclusion.app (op 0) ≫ initialAmbient.hom =
    initialIntrinsic.hom ≫ A.inclusion
  center : ∀ j : Fin n, (ambient.obj (op j.castSucc)).IdealSheafData
  centerToIntrinsic : ∀ j : Fin n, (center j).subscheme ⟶ intrinsic.obj (op j.castSucc)
  centerClosed : ∀ j, IsClosedImmersion (centerToIntrinsic j)
  centerInclusion : ∀ j, centerToIntrinsic j ≫ inclusion.app (op j.castSucc) =
    (center j).subschemeι
  ambientBlowup : ∀ j, ambient.obj (op j.succ) ≅ (center j).blowup
  ambientBlowupMap : ∀ j, (ambientBlowup j).hom ≫ (center j).blowupMap =
    ambient.map (homOfLE j.castSucc_le_succ).op
  strictTransform : ∀ j, intrinsic.obj (op j.succ) ≅
    (center j).strictTransform (inclusion.app (op j.castSucc))
  strictTransformMap : ∀ j, (strictTransform j).hom ≫ AlgebraicGeometry.strictTransformMap
    (inclusion.app (op j.castSucc)) (center j).blowupMap (center j).support.compl =
      inclusion.app (op j.succ) ≫ (ambientBlowup j).hom
  strictTransformToSource : ∀ j,
    (strictTransform j).hom ≫ AlgebraicGeometry.strictTransformToSource
      (inclusion.app (op j.castSucc)) (center j).blowupMap (center j).support.compl =
        intrinsic.map (homOfLE j.castSucc_le_succ).op

namespace EmbeddedResolutionHistory

/-- The final strict transform. Source: ILO VIII 2.3.11
(blueprint: def-trf-admissible-embedded-history). -/
def X {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n) :
    Scheme.{u} := H.intrinsic.obj (op (Fin.last n))

/-- The final ambient scheme. Source: ILO VIII 2.3.11
(blueprint: def-trf-admissible-embedded-history). -/
def P {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n) :
    Scheme.{u} := H.ambient.obj (op (Fin.last n))

/-- The final rational structure map, obtained from the recorded ordinary blowup maps.
Source: ILO VIII 2.3.11 (blueprint: def-trf-admissible-embedded-history). -/
def base {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n) :
    H.P ⟶ Spec (.of (ULift.{u} ℚ)) :=
  H.ambient.map (homOfLE (Fin.zero_le (Fin.last n))).op ≫ H.initialAmbient.hom ≫ A.base

/-- A one-step extension identifies the whole earlier ambient and strict-transform
history, not merely its final scheme. The ordered center ideals are preserved.
Source: ILO VIII 2.3.1, 2.3.11 (blueprint: def-trf-admissible-embedded-history). -/
structure Extension {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    (H : EmbeddedResolutionHistory A n) (K : EmbeddedResolutionHistory A (n + 1)) where
  ambient : ∀ j : Fin (n + 1), H.ambient.obj (op j) ≅ K.ambient.obj (op j.castSucc)
  intrinsic : ∀ j : Fin (n + 1), H.intrinsic.obj (op j) ≅ K.intrinsic.obj (op j.castSucc)
  inclusion : ∀ j, H.inclusion.app (op j) ≫ (ambient j).hom =
    (intrinsic j).hom ≫ K.inclusion.app (op j.castSucc)
  ambientNaturality : ∀ (j k : Fin (n + 1)) (h : j ≤ k),
    H.ambient.map (homOfLE h).op ≫ (ambient j).hom =
      (ambient k).hom ≫ K.ambient.map
        (homOfLE (Fin.castSucc_le_castSucc_iff.mpr h)).op
  intrinsicNaturality : ∀ (j k : Fin (n + 1)) (h : j ≤ k),
    H.intrinsic.map (homOfLE h).op ≫ (intrinsic j).hom =
      (intrinsic k).hom ≫ K.intrinsic.map
        (homOfLE (Fin.castSucc_le_castSucc_iff.mpr h)).op
  initialAmbient : (ambient 0).hom ≫ K.initialAmbient.hom = H.initialAmbient.hom
  initialIntrinsic : (intrinsic 0).hom ≫ K.initialIntrinsic.hom = H.initialIntrinsic.hom
  centers : ∀ j : Fin n, H.center j = (K.center j.castSucc).comap (ambient j.castSucc).hom

/-- The new center viewed in the old final strict transform. Source: ILO VIII 2.3.11
(blueprint: def-trf-admissible-embedded-history). -/
def Extension.centerMap {A : EmbeddedResolutionPair.{u}} {n : ℕ}
    {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
    (E : Extension H K) : (K.center (Fin.last n)).subscheme ⟶ H.X :=
  K.centerToIntrinsic (Fin.last n) ≫ (E.intrinsic (Fin.last n)).inv

/-- A stagewise smooth ambient pullback, deleting empty centers. The monotone surjection
`index` collapses exactly those transitions with unit pulled-back ideal. Every uncollapsed
transition preserves its actual ideal. Cartesian squares are over the initial schemes;
thus no arbitrary comparison map replaces the canonical base-change map.
Source: ILO VIII 2.3.4, 2.3.13; BMT 6.3
(blueprint: def-trf-admissible-embedded-history). -/
structure SmoothPullback {A B : EmbeddedResolutionPair.{u}} {m n : ℕ}
    (f : EmbeddedResolutionSmoothMap A B)
    (H : EmbeddedResolutionHistory A m) (K : EmbeddedResolutionHistory B n) where
  index : Fin (n + 1) →o Fin (m + 1)
  surjective : Function.Surjective index
  first : index 0 = 0
  last : index (Fin.last n) = Fin.last m
  ambient : ∀ j, H.ambient.obj (op (index j)) ⟶ K.ambient.obj (op j)
  intrinsic : ∀ j, H.intrinsic.obj (op (index j)) ⟶ K.intrinsic.obj (op j)
  inclusion : ∀ j, H.inclusion.app (op (index j)) ≫ ambient j =
    intrinsic j ≫ K.inclusion.app (op j)
  ambientNaturality : ∀ (j k : Fin (n + 1)) (h : j ≤ k),
    H.ambient.map (homOfLE (index.monotone h)).op ≫ ambient j =
      ambient k ≫ K.ambient.map (homOfLE h).op
  intrinsicNaturality : ∀ (j k : Fin (n + 1)) (h : j ≤ k),
    H.intrinsic.map (homOfLE (index.monotone h)).op ≫ intrinsic j =
      intrinsic k ≫ K.intrinsic.map (homOfLE h).op
  cartesianAmbient : ∀ j, IsPullback (ambient j)
    (H.ambient.map (homOfLE (Fin.zero_le (index j))).op ≫ H.initialAmbient.hom)
    (K.ambient.map (homOfLE (Fin.zero_le j)).op ≫ K.initialAmbient.hom) f.ambient
  cartesianIntrinsic : ∀ j, IsPullback (intrinsic j)
    (H.intrinsic.map (homOfLE (Fin.zero_le (index j))).op ≫ H.initialIntrinsic.hom)
    (K.intrinsic.map (homOfLE (Fin.zero_le j)).op ≫ K.initialIntrinsic.hom) f.intrinsic
  centers : ∀ j : Fin n,
    (index j.castSucc = index j.succ ∧ (K.center j).comap (ambient j.castSucc) = ⊤) ∨
      ∃ (k : Fin m) (h : index j.castSucc = k.castSucc),
        index j.succ = k.succ ∧ Nonempty (H.center k).subscheme ∧
          H.center k = (K.center j).comap
            (eqToHom (congrArg (fun t ↦ H.ambient.obj (op t)) h.symm) ≫ ambient j.castSucc)

/-- The final intrinsic map of a smooth history comparison, including deletion of all
stages. Source: ILO VIII 2.3.4, 2.3.13
(blueprint: def-trf-admissible-embedded-history). -/
def SmoothPullback.finalMap {A B : EmbeddedResolutionPair.{u}} {m n : ℕ}
    {f : EmbeddedResolutionSmoothMap A B}
    {H : EmbeddedResolutionHistory A m} {K : EmbeddedResolutionHistory B n}
    (c : SmoothPullback f H K) : H.X ⟶ K.X :=
  eqToHom (congrArg (fun t ↦ H.intrinsic.obj (op t)) c.last.symm) ≫ c.intrinsic (Fin.last n)

/-- Intrinsic history identification keeps every earlier center ideal and its order,
even when its intrinsic blowup was an identity. No isomorphism of the ambient schemes
is required. Pulling these ideals along the recorded diagram retains all exceptional data.
Source: ILO VIII 2.3.11--2.3.13; BMT 6.1 Addendum (3)
(blueprint: def-trf-admissible-embedded-history). -/
structure IntrinsicComparison {A B : EmbeddedResolutionPair.{u}} {n : ℕ}
    (e : A.X ≅ B.X) (H : EmbeddedResolutionHistory A n)
    (K : EmbeddedResolutionHistory B n) where
  iso : H.intrinsic ≅ K.intrinsic
  initial : (iso.app (op 0)).hom ≫ K.initialIntrinsic.hom = H.initialIntrinsic.hom ≫ e.hom
  centers : ∀ j : Fin n, (H.centerToIntrinsic j).ker =
    (K.centerToIntrinsic j).ker.comap (iso.app (op j.castSucc)).hom

/-- A simultaneous value assignment on raw histories. Conditions below concern only its
admissible histories; extension to other histories carries no mathematical assertion.
Source: ILO VIII 2.3.11--2.3.13 (blueprint: def-trf-admissible-embedded-history). -/
def ValueFamily (V : Type w) : Type (max (u + 1) w) :=
  ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ} (H : EmbeddedResolutionHistory A n), H.X → V

/-- A maximum step uses the reduced full positive maximum locus as its actual center.
Source: ILO VIII 2.3.11--2.3.13 (blueprint: def-trf-admissible-embedded-history). -/
def IsMaximumStep {V : Type w} [LinearOrder V] [OrderBot V] (ν : ValueFamily.{u} V)
    {A : EmbeddedResolutionPair.{u}} {n : ℕ} {H : EmbeddedResolutionHistory A n}
    {K : EmbeddedResolutionHistory A (n + 1)} (E : Extension H K) : Prop :=
  ∃ m : V, IsGreatest (Set.range (ν H)) m ∧ ⊥ < m ∧
    IsReduced (K.center (Fin.last n)).subscheme ∧
      Set.range E.centerMap = {x | ν H x = m}

/-- The least class generated by empty histories, reduced maximum-center steps, and
smooth ambient pullback with empty-center deletion. Open restriction is included because
an open immersion is smooth. This definition is relative to the simultaneous assignment,
so it does not assume an independently available resolution algorithm.
Source: ILO VIII 2.3.1, 2.3.4, 2.3.11--2.3.13
(blueprint: def-trf-admissible-embedded-history). -/
inductive Admissible {V : Type w} [LinearOrder V] [OrderBot V] (ν : ValueFamily.{u} V) :
    ∀ {A : EmbeddedResolutionPair.{u}} {n : ℕ}, EmbeddedResolutionHistory A n → Prop
  | empty {A : EmbeddedResolutionPair.{u}} (H : EmbeddedResolutionHistory A 0) : Admissible ν H
  | step {A : EmbeddedResolutionPair.{u}} {n : ℕ}
      {H : EmbeddedResolutionHistory A n} {K : EmbeddedResolutionHistory A (n + 1)}
      (E : Extension H K) : Admissible ν H → IsMaximumStep ν E → Admissible ν K
  | pullback {A B : EmbeddedResolutionPair.{u}} {m n : ℕ}
      {H : EmbeddedResolutionHistory A m} {K : EmbeddedResolutionHistory B n}
      (f : EmbeddedResolutionSmoothMap A B) (c : SmoothPullback f H K) :
        Admissible ν K → Admissible ν H

end EmbeddedResolutionHistory
end AlgebraicGeometry
