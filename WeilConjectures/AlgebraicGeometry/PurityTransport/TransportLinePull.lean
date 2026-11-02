/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.PurityTransport.TransportDerived

/-! # Purity transport statement interfaces

Source: current blueprint sk-thm-purity-transport, canonical comparison clauses.
(blueprint: def-pur-transport-line-pullback). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.PurityTransport
variable (ell : ℕ) [Fact ell.Prime]

/-- Coordinates for the root-normalized pullback of the Tate line. Each comparison
is specified by a canonical construction; none is an arbitrary root frame.
Source: Cartesian coefficients (blueprint: def-pur-transport-line-pullback). -/
structure LinePullCoordinates (c : Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y) where
  integral : (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).obj
    (tateModule Y ell) ≅ tateModule X ell
  integral_normalized : ∀ n : ℕ, ∃ en :
    (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).obj
      (tateModuleLevel Y ell n) ≅ tateModuleLevel X ell n,
    PullNormalized (Profinite.continuousMapRingObj ℤ_[ell]) f en
      (rootTensorPull ell f n) ∧
    integral.hom ≫ limit.π (tateModuleSystem X ell) (Opposite.op n) =
      (CondensedRing.upperStar (Profinite.continuousMapRingObj ℤ_[ell]) f).map
        (limit.π (tateModuleSystem Y ell) (Opposite.op n)) ≫ en.hom
  first : (CondensedRing.upperStar (c.obj ell) f).obj
    (c.firstLine ell Y) ≅ c.firstLine ell X
  first_normalized : HEq first (scalarPull (c.integralMap ell) f integral)
  power : ∀ d : ℕ, (CondensedRing.upperStar (c.obj ell) f).obj
    (c.line ell Y d) ≅ c.line ell X d
  power_normalized : ∀ d : ℕ, HEq (power d)
    (powerPull (CondensedRing.upperStar (c.obj ell) f)
      (c.firstLine ell Y) (c.firstLine ell X) first d)

/-- Shifted derived Tate pullback from the normalized ordinary coordinates.
Source: Cartesian twists (blueprint: def-pur-transport-line-pullback). -/
def LinePullCoordinates.derived {c : Coefficient ell} {X Y : Scheme.{u}}
    {f : X ⟶ Y} (p : LinePullCoordinates ell c f) (d : ℕ) :=
  derivedPull ell c f d (p.power d)

/-- Existence of the normalized root coordinates, including the zeroth tensor power.
Source: Cartesian twists (blueprint: def-pur-transport-line-pullback).
Proof: take the projection-normalized integral comparison. Apply scalar association
and the monoidal inverse-image tensorators, recursively in the tensor power.
The three normalization fields are their defining equations. -/
theorem linePullCoordinates_nonempty (c : Coefficient ell) {X Y : Scheme.{u}} (f : X ⟶ Y)
    [∀ x : X, Invertible (ell : X.residueField x)]
    [∀ y : Y, Invertible (ell : Y.residueField y)] :
    Nonempty (LinePullCoordinates ell c f) := by
  obtain ⟨e, he, _⟩ := integralComparison ell f
  let first := scalarPull (c.integralMap ell) f e
  have line_eq (Z : Scheme.{u}) (d : ℕ) :
      c.line ell Z d = Nat.rec (𝟙_ _) (fun _ N ↦ N ⊗ c.firstLine ell Z) d := by
    induction d with
    | zero => rfl
    | succ d ih => exact congrArg (fun N ↦ N ⊗ c.firstLine ell Z) ih
  have powers (d : ℕ) : ∃ p :
      (CondensedRing.upperStar (c.obj ell) f).obj (c.line ell Y d) ≅ c.line ell X d,
      HEq p (powerPull (CondensedRing.upperStar (c.obj ell) f)
        (c.firstLine ell Y) (c.firstLine ell X) first d) := by
    rw [line_eq Y d, line_eq X d]
    exact ⟨_, HEq.rfl⟩
  choose power hpower using powers
  exact ⟨{ integral := e
           integral_normalized := he
           first := first
           first_normalized := HEq.rfl
           power := power
           power_normalized := hpower }⟩

end AlgebraicGeometry.ProEtale.PurityTransport
