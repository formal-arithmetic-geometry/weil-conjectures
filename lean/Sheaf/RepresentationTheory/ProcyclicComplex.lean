/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF worker E6
-/
module

public import WeilConjectures.RepresentationTheory.DiscreteContinuousRep
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The explicit two-term complex of an action

Source: blueprint, lem-exc-procyclic-two-term, first proof paragraph.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace Rep

variable (A : Type u) [Ring A] (G : Type v) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]

/-- Terms of the two-term action complex. -/
def actionTwoTermX (M : DiscreteContinuousRep.{u, v, w} A G) : ℕ → ModuleCat.{w} A
  | 0 => (ModuleCat.of A M.obj.V : ModuleCat.{w} A)
  | 1 => (ModuleCat.of A M.obj.V : ModuleCat.{w} A)
  | _ + 2 => ModuleCat.of A PUnit.{w + 1}

/-- Its sole nonzero differential is the action of `τ` minus the identity. -/
def actionTwoTermD (τ : G) (M : DiscreteContinuousRep.{u, v, w} A G) :
    ∀ n : ℕ, actionTwoTermX A G M n ⟶ actionTwoTermX A G M (n + 1)
  | 0 => ModuleCat.ofHom (M.obj.ρ τ - LinearMap.id)
  | _ + 1 => 0

/-- The complex is explicitly constructed, without selecting any existence witness. -/
def actionTwoTermObj (τ : G) (M : DiscreteContinuousRep.{u, v, w} A G) :
    CochainComplex (ModuleCat.{w} A) ℕ :=
  CochainComplex.of (actionTwoTermX A G M) (actionTwoTermD A G τ M)
    (by intro n; cases n <;> simp [actionTwoTermD])

/-- The same coefficient map in degrees zero and one, and zero elsewhere. -/
def actionTwoTermMap (τ : G) {M N : DiscreteContinuousRep.{u, v, w} A G}
    (f : M ⟶ N) : actionTwoTermObj A G τ M ⟶ actionTwoTermObj A G τ N :=
  CochainComplex.ofHom
    (fun n ↦ match n with
      | 0 => ModuleCat.ofHom f.hom.hom.toLinearMap
      | 1 => ModuleCat.ofHom f.hom.hom.toLinearMap
      | _ + 2 => 0)
    (by
      intro n
      cases n with
      | zero =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        change M.obj.V at x
        change (N.obj.ρ τ) (f.hom.hom x) - f.hom.hom x =
          f.hom.hom (M.obj.ρ τ x - x)
        rw [map_sub]
        exact congrArg (fun y ↦ y - f.hom.hom x) (Rep.hom_comm_apply f.hom τ x).symm
      | succ n =>
        simp [actionTwoTermObj, CochainComplex.of_d, actionTwoTermD])

/-- The functorial two-term action complex with differential action minus identity.

The coefficient map is used in both nonzero degrees; equivariance is exactly the
chain-map equation, and all remaining maps have zero source or target.
Source: blueprint lem-exc-procyclic-two-term, first proof paragraph
(blueprint: def-exc-action-two-term-complex). -/
def actionTwoTerm (τ : G) : DiscreteContinuousRep.{u, v, w} A G ⥤
    CochainComplex (ModuleCat.{w} A) ℕ where
  obj := actionTwoTermObj A G τ
  map := actionTwoTermMap A G τ
  map_id M := by
    ext n
    cases n with
    | zero => rfl
    | succ n => cases n <;> simp [actionTwoTermMap, actionTwoTermObj, actionTwoTermX]
  map_comp f g := by
    ext n
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n => simp [actionTwoTermMap]

/-- Degree zero is the coefficient module. -/
noncomputable def actionTwoTermEquivZero (τ : G) (M : DiscreteContinuousRep.{u, v, w} A G) :
    ((actionTwoTerm A G τ).obj M).X 0 ≃ₗ[A] M.obj.V := LinearEquiv.refl A _

/-- Degree one is the coefficient module. -/
noncomputable def actionTwoTermEquivOne (τ : G) (M : DiscreteContinuousRep.{u, v, w} A G) :
    ((actionTwoTerm A G τ).obj M).X 1 ≃ₗ[A] M.obj.V := LinearEquiv.refl A _

/-- There are no terms above degree one. -/
theorem actionTwoTerm_isZero (τ : G) (M : DiscreteContinuousRep.{u, v, w} A G)
    (n : ℕ) (hn : 2 ≤ n) : IsZero (((actionTwoTerm A G τ).obj M).X n) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hn
  change IsZero (actionTwoTermX A G M (2 + n))
  rw [Nat.add_comm]
  exact ModuleCat.isZero_iff_subsingleton.mpr (by
    change Subsingleton PUnit.{w + 1}
    infer_instance)

end Rep
