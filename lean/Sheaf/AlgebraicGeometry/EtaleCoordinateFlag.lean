module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

public import Mathlib.AlgebraicGeometry.AffineSpace
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Simultaneous étale coordinates for a closed flag and an ordered boundary

Source: Stacks Project, More on Morphisms, Tag 0FUE, and the simultaneous-coordinate
hypothesis of the marked blowup calculation (blueprint: def-trf-etale-coordinate-flag).
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- The given closed flag and labelled divisors are coordinate subspaces and distinct
coordinate hyperplanes on an affine étale neighbourhood of every point. A member absent
near that point has unit ideal. The normal coordinates of `N` are disjoint from the
boundary coordinates; the center coordinates may include boundary coordinates.
Source: Stacks Project, Tag 0FUE, with the explicit simultaneous flag hypothesis
(blueprint: def-trf-etale-coordinate-flag). -/
def HasEtaleCoordinateFlag {Z : Scheme.{u}} (p : Z ⟶ Spec (.of (ULift.{u} ℚ)))
    (N C : Z.IdealSheafData) (E : List Z.IdealSheafData) : Prop :=
  N ≤ C ∧ ∀ x : Z, ∃ (W : Scheme.{u}) (q : W ⟶ Z) (n : ℕ)
    (v : Fin n → Γ(W, ⊤)) (B A : Finset (Fin n))
    (b : Fin E.length → Option (Fin n)),
    IsAffine W ∧ Etale q ∧ x ∈ Set.range q ∧
    Etale (AffineSpace.homOfVector (q ≫ p) (fun i : ULift.{u} (Fin n) ↦ v i.down)) ∧
    B ⊆ A ∧
    (x ∈ N.support → N.comap q =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span (v '' (B : Set (Fin n))))) ∧
    (x ∉ N.support → N.comap q = ⊤) ∧
    (x ∈ C.support → C.comap q =
      Scheme.IdealSheafData.ofIdealTop (Ideal.span (v '' (A : Set (Fin n))))) ∧
    (x ∉ C.support → C.comap q = ⊤) ∧
    (∀ j : Fin E.length, (E.get j).comap q = match b j with
      | none => ⊤
      | some a => Scheme.IdealSheafData.ofIdealTop (Ideal.span {v a})) ∧
    (∀ (j k : Fin E.length) (a : Fin n), b j = some a → b k = some a → j = k) ∧
    (∀ (j : Fin E.length) (a : Fin n), b j = some a → a ∉ B)

end AlgebraicGeometry
