/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoefficientHeartTower.CoefficientHeartGaloisSequence
public import WeilConjectures.AlgebraicGeometry.CoefficientHeartTower.FinitePointedTower.CoefficientHeartTowerSchemeLimit
public import WeilConjectures.AlgebraicGeometry.FundamentalGroup.Connected

/-! # Finite pointed scheme stages from nested Galois representatives

Source: coefficient-heart proof (1), connected finite etale trivializing covers.
(blueprint: lem-sfb-coefficient-heart-finite-stages)
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.PreGaloisCategory Opposite
namespace AlgebraicGeometry.ProEtale.CoefficientHeartTower
variable {X : Scheme.{u}} [ConnectedSpace X]
variable {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

omit [ConnectedSpace X] in
/-- A map of finite etale covers with connected target and nonempty source is surjective.
Source: coefficient-heart proof (1), open and closed images of the transition maps.
(blueprint: lem-sfb-coefficient-heart-finite-stages)
Proof: its image is closed by finiteness and open by etaleness. It is nonempty, hence
is the entire connected target. Finiteness and etaleness of the map follow by cancellation
from the structure maps to the base. -/
theorem finiteEtale_transition_surjective {P Q : X.FiniteEtale}
    [Nonempty P.obj.left] [ConnectedSpace Q.obj.left] (f : P ⟶ Q) :
    Surjective f.hom.left := by
  have hc : IsClopen (Set.range f.hom.left) :=
    ⟨f.hom.left.isClosedMap.isClosed_range, f.hom.left.isOpenMap.isOpen_range⟩
  obtain ⟨p⟩ := (inferInstance : Nonempty P.obj.left)
  exact ⟨Set.range_eq_univ.mp (hc.eq_univ ⟨_, p, rfl⟩)⟩

/-- A sequence of pointed Galois representatives is a pointed connected finite etale tower.
Source: coefficient-heart proof (1), descending the nested finite monodromy quotients.
(blueprint: lem-sfb-coefficient-heart-finite-stages)
The diagram is the actual sequence of finite etale objects with the supplied adjacent maps.
All structure and transition maps are finite, etale and surjective; the geometric points
are the chosen fibre elements, whose coherence is exactly the sequence's point equation. -/
def GaloisSequence.toFinitePointedTower (v : Spec (.of Ω) ⟶ X) {E : ℕ → X.FiniteEtale}
    (s : GaloisSequence (Scheme.FiniteEtale.fiber v) E) : FinitePointedTower v := by
  have hg (n : ℕ) : IsGalois (s.stage n).obj := (s.stage n).galois
  have hc (n : ℕ) : ConnectedSpace (s.stage n).obj.obj.left :=
    Scheme.FiniteEtale.connectedSpace_of_isConnected (s.stage n).obj
  let D := Functor.ofOpSequence (X := fun n ↦ (s.stage n).obj) s.arrow
  refine
    { diagram := D ⋙ ObjectProperty.ι _ ⋙ Scheme.Etale.forget X
      finite := fun n ↦ (s.stage n).obj.property
      etale := fun n ↦ (s.stage n).obj.obj.prop
      surjective := fun n ↦ Scheme.FiniteEtale.surjective_of_nonempty_fiber v
        (s.stage n).obj ⟨(s.stage n).point⟩
      connected := hc
      transitionFinite := ?_
      transitionEtale := ?_
      transitionSurjective := ?_
      point := fun n ↦ (s.stage n).point.left
      point_base := fun n ↦ Scheme.FiniteEtale.fiber_left_comp v (s.stage n).point
      point_transition := ?_ }
  · intro n
    change IsFinite ((D.map (homOfLE (Nat.le_succ n)).op).hom.left)
    dsimp only [D]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    infer_instance
  · intro n
    change Etale ((D.map (homOfLE (Nat.le_succ n)).op).hom.left)
    dsimp only [D]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    infer_instance
  · intro n
    change Surjective ((D.map (homOfLE (Nat.le_succ n)).op).hom.left)
    dsimp only [D]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact finiteEtale_transition_surjective (s.arrow n)
  · intro n
    change (s.stage (n + 1)).point.left ≫
      (D.map (homOfLE (Nat.le_succ n)).op).hom.left = (s.stage n).point.left
    dsimp only [D]
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact (Scheme.FiniteEtale.fiber_map_left v (s.arrow n)
      (s.stage (n + 1)).point).symm.trans
        (congrArg (fun p ↦ p.left) (s.point_arrow n))

end AlgebraicGeometry.ProEtale.CoefficientHeartTower
