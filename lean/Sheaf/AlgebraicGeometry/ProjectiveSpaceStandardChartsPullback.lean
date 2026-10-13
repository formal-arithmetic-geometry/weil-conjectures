/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfSections
public import Sheaf.AlgebraicGeometry.TensorPullbackAdjunction

/-!
# Standard charts and coordinate sections of projective space

Source: Stacks Project, Tags 01NG, 01MV, 01MS, 01ND, 01JR and 01I4
(blueprint: lem-weil-pbc-projective-space-standard-charts-part1).
-/

@[expose] public section

universe u

open CategoryTheory Opposite
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.ProjectiveSpace

noncomputable section

attribute [local instance] MvPolynomial.gradedAlgebra

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Coordinate sections freely generate the tensor pullback on each standard chart and
satisfy the coordinate-ratio relation.
Source: Stacks Project, Constructions, Tags 01MS and 01MV; Modules, Tag 0096.
(blueprint: lem-weil-pbc-projective-space-standard-charts-part1).

Proof: The adjunction defining tensorPullback and the usual pullback adjunction have the
same right adjoint. Uniqueness of left adjoints gives an isomorphism e of their values
on O(1), and compatibility with units sends every pulled coordinate section to the usual
pullbackSection. Naturality of e gives this equality after restriction to every open.
Transport invertibility through e. On the i-th chart the upstream theorem
isFreeGenerator_pullbackSection_twistOneSection gives a free generator; restrict it to
V and use its bijective scalar multiplication map to get the unique coefficient of e(t).
Injectivity of e on sections transports both existence and uniqueness back. Finally,
apply e to the desired ratio relation, use its linearity and unit compatibility, and
apply pullbackSection_twistOneSection_map_eq_smul with indices j,i. -/
theorem projectiveSpace_standardCharts_part1 (n : Type u) (S : Scheme.{u})
    [Finite n] [Nonempty n] :
    (∀ (Y : Scheme.{u}) (g : Y ⟶ ℙ(n; S)) (i j : n),
      ((Scheme.Modules.tensorPullback g).obj (twist n S 1)).IsInvertible ∧
      (∀ (V : Y.Opens), V ≤ g ⁻¹ᵁ standardOpen n S i →
        ∀ t : Γ((Scheme.Modules.tensorPullback g).obj (twist n S 1), V),
          ∃! a : Γ(Y, V), t = a •
            ((Scheme.Modules.tensorPullback g).obj (twist n S 1)).presheaf.map
              (homOfLE (le_top : V ≤ ⊤)).op 
                (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
                  (twist n S 1)).val.app (op ⊤) (twistOneSection n S i))) ∧
      ((Scheme.Modules.tensorPullback g).obj (twist n S 1)).presheaf.map
          (homOfLE (le_top : g ⁻¹ᵁ standardOpen n S i ≤ ⊤)).op 
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
              (twist n S 1)).val.app (op ⊤) (twistOneSection n S j)) =
        g.app (standardOpen n S i)
          ((toProjInt n S).app
            (Proj.basicOpen (MvPolynomial.homogeneousSubmodule n (ULift.{u} ℤ)) (MvPolynomial.X i))
            (Proj.awayToSection _ _ (MvPolynomial.awayXRatio (ULift.{u} ℤ) i j))) •
          ((Scheme.Modules.tensorPullback g).obj (twist n S 1)).presheaf.map
            (homOfLE (le_top : g ⁻¹ᵁ standardOpen n S i ≤ ⊤)).op 
                (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)).unit.app
                  (twist n S 1)).val.app (op ⊤) (twistOneSection n S i))) := by
  classical
  intro Y g i j
  let adj := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction g)
  let e := (adj.leftAdjointUniq (pullbackPushforwardAdjunction g)).app (twist n S 1)
  let L := (Scheme.Modules.tensorPullback g).obj (twist n S 1)
  have hs (k : n) (V : Y.Opens) :
      e.hom.app V (L.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((adj.unit.app (twist n S 1)).val.app (op ⊤) (twistOneSection n S k))) =
      ((Scheme.Modules.pullback g).obj (twist n S 1)).presheaf.map
        (homOfLE (le_top : V ≤ ⊤)).op (pullbackSection g (twistOneSection n S k)) := by
    rw [Hom.app_presheaf_map]
    congr 1
    exact congrArg (fun t ↦ t.val.app (op ⊤) (twistOneSection n S k))
      (adj.unit_leftAdjointUniq_hom_app (pullbackPushforwardAdjunction g) (twist n S 1))
  have hi : L.IsInvertible := IsInvertible.of_iso e.symm
  refine ⟨hi, ?_, ?_⟩
  · intro V hV t
    have hg := (isFreeGenerator_pullbackSection_twistOneSection (n := n) (S := S) g i).map hV
    rw [presheaf_map_map_apply] at hg
    have ht := hg.bijective
    obtain ⟨a, ha⟩ := ht.2 (e.hom.app V t)
    refine ⟨a, ?_, ?_⟩
    · apply (ConcreteCategory.bijective_of_isIso (e.hom.app V)).1
      rw [Hom.app_smul, hs]
      exact ha.symm
    · intro b hb
      apply ht.1
      have hb' := congrArg (e.hom.app V) hb
      rw [Hom.app_smul, hs] at hb'
      exact hb'.symm.trans ha.symm
  · apply (ConcreteCategory.bijective_of_isIso
      (e.hom.app (g ⁻¹ᵁ standardOpen n S i))).1
    rw [Hom.app_smul, hs, hs]
    exact pullbackSection_twistOneSection_map_eq_smul g j i

end
end AlgebraicGeometry.ProjectiveSpace
