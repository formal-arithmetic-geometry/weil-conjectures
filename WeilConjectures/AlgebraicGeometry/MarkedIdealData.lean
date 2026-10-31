/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.HilbertSamuelPresentation
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Invertible
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Algebra.Field.ULift

/-!
# Rational marked inputs and their ordered histories

Source: Bierstone--Milman--Temkin, arXiv:0905.3580, sections 5.1--5.2;
ILO VIII 2.3.11--2.3.13 (blueprint: def-trf-marked-ideal-data).

The marked ideals, orders, adapted centers, test operations and their equivalence are
those of the existing Hilbert--Samuel presentation interface. This module only packages
its finite-type rational inputs and adds ordered histories and their birth bookkeeping.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Finite-type rational inputs for the numerical engine, using the existing embedded
and marked data. SNC is the existing adapted-center condition for the bottom ideal,
whose vanishing locus is the entire scheme. Transversality uses the same predicate on N.
No Hilbert--Samuel presentation or retained-level condition is required of the marked ideal.
Source: BMT section 5.1 (blueprint: def-trf-marked-ideal-data). -/
structure MarkedIdeal where
  ambient : HilbertSamuel.Embedded (ULift.{u} ℚ)
  marked : HilbertSamuel.Marked ambient
  finiteTypeAmbient : LocallyOfFiniteType ambient.p
  compactAmbient : QuasiCompact ambient.p
  finiteTypeSupport : LocallyOfFiniteType (marked.j ≫ ambient.p)
  compactSupport : QuasiCompact (marked.j ≫ ambient.p)
  cartier : ∀ D ∈ ambient.boundary, D.IsInvertible
  snc : HasAdaptedNormalCrossingsCenter (⊥ : ambient.Z.IdealSheafData)
    (fun i ↦ ambient.boundary.get i)
  smoothBoundary : ∀ D ∈ ambient.boundary, Smooth (D.subschemeι ≫ ambient.p)
  transverseCartier : ∀ D ∈ ambient.boundary, (D.comap marked.j).IsInvertible
  transverse : HasAdaptedNormalCrossingsCenter (⊥ : marked.N.IdealSheafData)
    (fun i ↦ (ambient.boundary.get i).comap marked.j)

namespace MarkedIdeal

/-- Cosupport viewed on the smooth support, by inverse image of the existing ambient
cosupport. The closed immersion is injective, so this is exactly order at least the mark.
Source: BMT section 5.1 (blueprint: def-trf-marked-ideal-data). -/
def cosupport (A : MarkedIdeal.{u}) : Set A.marked.N :=
  A.marked.j ⁻¹' A.marked.cosupport

/-- Exact marked order on cosupport, using the existing extended-natural order.
Source: BMT section 5.1 (blueprint: def-trf-marked-ideal-data). -/
def IsMaximalOrder (A : MarkedIdeal.{u}) : Prop :=
  ∀ x ∈ A.cosupport, HilbertSamuel.order A.marked.ideal x = (A.marked.marking : ℕ∞)

/-- One controlled history stage uses the existing admissible operation and transform.
The support and center maps are retained for history comparisons. Their commuting
triangles with the closed immersion determine them uniquely; they are not arbitrary maps.
Smoothness and adapted normal crossings of the center are in `step.geometry`.
Source: BMT sections 5.1--5.2 (blueprint: def-trf-marked-ideal-data). -/
structure HistoryStep (A B : MarkedIdeal.{u}) where
  step : HilbertSamuel.Step A.ambient B.ambient
  kind : step.kind = .admissibleBlowup
  admissible : step.Admissible A.marked.cosupport
  transforms : step.Transforms A.marked B.marked
  support : B.marked.N ⟶ A.marked.N
  square : support ≫ A.marked.j = B.marked.j ≫ step.π
  centerToSupport : step.center.subscheme ⟶ A.marked.N
  centerTriangle : centerToSupport ≫ A.marked.j = step.center.subschemeι
  exceptionalInvertible : ((step.center.comap step.π).comap B.marked.j).IsInvertible

/-- A finite history of existing controlled transforms, with the boundary birth stages.
Original members are born at zero and each new exceptional member at its blowup stage.
Source: BMT sections 5.1--5.2; BM invariant history bookkeeping
(blueprint: def-trf-marked-ideal-data). -/
structure History (n : ℕ) where
  state : Fin (n + 1) → MarkedIdeal.{u}
  step : ∀ i : Fin n, HistoryStep (state i.castSucc) (state i.succ)
  birth : ∀ i, Fin (state i).ambient.boundary.length → ℕ
  initialBirth : ∀ j, birth 0 j = 0
  inheritedBirth : ∀ (i : Fin n) (j : Fin (state i.castSucc).ambient.boundary.length)
    (k : Fin (state i.succ).ambient.boundary.length), j.val = k.val →
      birth i.succ k = birth i.castSucc j
  exceptionalBirth : ∀ (i : Fin n) (k : Fin (state i.succ).ambient.boundary.length),
    k.val = (state i.castSucc).ambient.boundary.length → birth i.succ k = i.val + 1

/-- The final input of a finite history.
Source: BMT section 5.1 (blueprint: def-trf-marked-ideal-data). -/
def History.last {n : ℕ} (H : History.{u} n) : MarkedIdeal.{u} := H.state (Fin.last n)

/-- Extension retains all preceding marked inputs, actual operations and birth stages.
Source: BMT sections 5.1--5.2 (blueprint: def-trf-marked-ideal-data). -/
structure Extension {n : ℕ} (H : History.{u} n) (K : History.{u} (n + 1)) where
  states : ∀ i, H.state i = K.state i.castSucc
  steps : ∀ i : Fin n, HEq (H.step i) (K.step i.castSucc)
  births : ∀ i, HEq (H.birth i) (K.birth i.castSucc)

/-- The next center on the old support, using the extension identification.
Source: BMT section 5.1 (blueprint: def-trf-marked-ideal-data). -/
def Extension.centerMap {n : ℕ} {H : History.{u} n} {K : History.{u} (n + 1)}
    (E : Extension H K) : (K.step (Fin.last n)).step.center.subscheme ⟶ H.last.marked.N :=
  (K.step (Fin.last n)).centerToSupport ≫
    eqToHom (congrArg (fun A : MarkedIdeal.{u} ↦ A.marked.N)
      (E.states (Fin.last n)).symm)

/-- The next canonical support map, transported by the extension identification.
Source: BMT section 5.1 (blueprint: def-trf-marked-ideal-data). -/
def Extension.supportMap {n : ℕ} {H : History.{u} n} {K : History.{u} (n + 1)}
    (E : Extension H K) : K.last.marked.N ⟶ H.last.marked.N :=
  (K.step (Fin.last n)).support ≫
    eqToHom (congrArg (fun A : MarkedIdeal.{u} ↦ A.marked.N)
      (E.states (Fin.last n)).symm)

/-- Smooth pullback of a history uses the existing marked-pullback relation at every
stage. The displayed cartesian map is retained for value comparisons, and its triangle
with the closed immersion pins it to the map in that relation. Relative dimensions may
vary. Empty pulled-back centers remain as empty stages.
Source: BMT Remark 5.1 and section 5.2 (blueprint: def-trf-marked-ideal-data). -/
structure HistoryPullback {n : ℕ} (H K : History.{u} n) where
  ambient : ∀ i, (H.state i).ambient.Z ⟶ (K.state i).ambient.Z
  support : ∀ i, (H.state i).marked.N ⟶ (K.state i).marked.N
  smooth : ∀ i, Smooth (ambient i)
  base : ∀ i, ambient i ≫ (K.state i).ambient.p = (H.state i).ambient.p
  marked : ∀ i, HilbertSamuel.MarkedPullback (ambient i)
    (K.state i).marked (H.state i).marked
  cartesian : ∀ i, IsPullback (support i) (H.state i).marked.j
    (K.state i).marked.j (ambient i)
  boundary : ∀ i, (H.state i).ambient.boundary =
    (K.state i).ambient.boundary.map (fun D ↦ D.comap (ambient i))
  ambientNaturality : ∀ i : Fin n,
    (H.step i).step.π ≫ ambient i.castSucc = ambient i.succ ≫ (K.step i).step.π
  centers : ∀ i : Fin n,
    (H.step i).step.center = (K.step i).step.center.comap (ambient i.castSucc)
  births : ∀ (i : Fin (n + 1)) (j : Fin (H.state i).ambient.boundary.length)
    (k : Fin (K.state i).ambient.boundary.length),
      j.val = k.val → H.birth i j = K.birth i k

/-- Identified ambient histories with equivalent marked presentations. Pull back the
second marked ideal through the ambient isomorphism using `MarkedPullback`, then use
Q79's depth-wise `Equivalent` on that common ambient. Thus cosupports agree at every
finite test depth, including the existence of every transform. The auxiliary embedded
schemes and retained Hilbert--Samuel levels impose no presentation condition here.
Source: BMT sections 5.1--5.4 (blueprint: def-trf-marked-ideal-data). -/
structure HistoryEquivalence {n : ℕ} (H K : History.{u} n) where
  ambient : ∀ i, (H.state i).ambient.Z ≅ (K.state i).ambient.Z
  base : ∀ i, (ambient i).hom ≫ (K.state i).ambient.p = (H.state i).ambient.p
  boundary : ∀ i, (H.state i).ambient.boundary =
    (K.state i).ambient.boundary.map (fun D ↦ D.comap (ambient i).hom)
  comparison : ∀ i, HilbertSamuel.Marked (H.state i).ambient
  comparisonPullback : ∀ i, HilbertSamuel.MarkedPullback (ambient i).hom
    (K.state i).marked (comparison i)
  equivalent : ∀ i, HilbertSamuel.Equivalent (H.state i).marked (comparison i)
  centers : ∀ i : Fin n, (H.step i).step.center =
    (K.step i).step.center.comap (ambient i.castSucc).hom
  naturality : ∀ i : Fin n,
    (H.step i).step.π ≫ (ambient i.castSucc).hom =
      (ambient i.succ).hom ≫ (K.step i).step.π
  births : ∀ (i : Fin (n + 1)) (j : Fin (H.state i).ambient.boundary.length)
    (k : Fin (K.state i).ambient.boundary.length),
      j.val = k.val → H.birth i j = K.birth i k

end MarkedIdeal
end AlgebraicGeometry
