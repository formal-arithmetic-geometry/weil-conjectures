/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.System.SystemRingedSequenceSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses

/-! # Levelwise flat strict systems are flat on the sequence site

Source: Zheng, Construction 4.1; Stacks Project, Tag 08FC (auxiliary; not a blueprint node).

A strict semilinear system whose levels are flat module sheaves gives a flat module sheaf on
the ringed sequence site. The proof uses the local equational criterion: a relation at
`(n, U)` is a relation in the level `n`, and the local witnesses at level `n` restrict
horizontally to every lower level.
-/

@[expose] public noncomputable section
set_option autoImplicit false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace SheafOfModules
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [EssentiallySmall.{w} C]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Vertical restriction in the sequence ring is restriction in the level ring.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
theorem systemSequenceRing_vertical (n : ℕ) {U V : C} (f : V ⟶ U)
    (a : (B.obj (op n)).obj.obj (op U)) :
    (systemSequenceRing B).obj.map ((Prod.sectR n C).map f).op a =
      (B.obj (op n)).obj.map f.op a := by
  exact congrArg (fun y ↦ (B.obj (op n)).obj.map f.op y)
    (congrArg (fun φ : B.obj (op n) ⟶ B.obj (op n) ↦ φ.hom.app (op U) a) (B.map_id (op n)))

/-- Vertical restriction of the associated sequence sheaf is restriction in the level.
Source: Zheng 4.1 (auxiliary; not a blueprint node). -/
theorem strictSystemToSequence_vertical (M : StrictRingSystem B) (n : ℕ) {U V : C}
    (f : V ⟶ U) (x : (M.level n).val.obj (op U)) :
    (strictSystemToSequence B M).val.map ((Prod.sectR n C).map f).op x =
      (M.level n).val.map f.op x := by
  exact congrArg (fun y ↦ (M.level n).val.map f.op y) (M.identity n (op U) x)

/-- A strict system with flat levels is flat on the ringed sequence site.
Source: Zheng 4.1; Stacks 08FC (auxiliary; not a blueprint node).
Proof: by the local equational criterion. A relation at `(n, U)` is a relation in level
`n`; flatness of that level factors it on a covering sieve of `U`. The sieve of arrows
whose vertical component lies in it covers `(n, U)`, and the factorization restricts
along the horizontal component of each such arrow. -/
theorem strictSystemToSequence_isFlatOnSite
    [(coefficientSequenceTopology J).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify (coefficientSequenceTopology J) AddCommGrpCat.{w}]
    (M : StrictRingSystem B)
    (hM : ∀ n : ℕ, IsFlatOnSite (J := J) (R := B.obj (op n)) (M.level n)) :
    IsFlatOnSite (J := coefficientSequenceTopology J) (R := systemSequenceRing B)
      ((strictSystemSequenceEquivalence B).functor.obj M) := by
  apply isFlatOnSite_of_local_equationalCriterion
  rintro ⟨n, U⟩ k a s hs
  obtain ⟨S, hS, h⟩ := local_equationalCriterion_of_isFlatOnSite.{u, v, w, w}
    (B.obj (op n)) (M.level n) (hM n) U k a s hs
  let T : Sieve ((n, U) : ℕ × C) :=
    { arrows := fun _ g ↦ S g.2
      downward_closed := fun hg g' ↦ S.downward_closed hg g'.2 }
  refine ⟨T, hS, ?_⟩
  rintro ⟨m, V⟩ g hg
  obtain ⟨l, b, t, ht, hb⟩ := h V g.2 hg
  let q : ((m, V) : ℕ × C) ⟶ (n, V) := Prod.mkHom g.1 (𝟙 V)
  have hq : q ≫ (Prod.sectR n C).map g.2 = g := by
    ext
    · exact Subsingleton.elim _ _
    · simp [q]
  refine ⟨l, fun p j ↦ (systemSequenceRing B).obj.map q.op (b p j),
    fun j ↦ (strictSystemToSequence B M).val.map q.op (t j), ?_, ?_⟩
  · intro p
    let N := strictSystemToSequence B M
    calc N.val.map g.op (s p)
        = N.val.map q.op (N.val.map ((Prod.sectR n C).map g.2).op (s p)) := by
          conv_lhs => rw [← hq]
          rw [op_comp, PresheafOfModules.map_comp_apply]
          rfl
      _ = N.val.map q.op (∑ j : Fin l, b p j • t j) := by
          rw [strictSystemToSequence_vertical, ht p]
      _ = _ := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun j _ ↦ PresheafOfModules.map_smul _ _ _ _
  · intro j
    have hg (p : Fin k) : (systemSequenceRing B).obj.map g.op (a p) =
        (systemSequenceRing B).obj.map q.op ((B.obj (op n)).obj.map g.2.op (a p)) := by
      conv_lhs => rw [← hq]
      rw [op_comp, Functor.map_comp, CommRingCat.comp_apply]
      exact congrArg (fun y ↦ (systemSequenceRing B).obj.map q.op y)
        (systemSequenceRing_vertical B n g.2 (a p))
    calc ∑ p : Fin k, (systemSequenceRing B).obj.map g.op (a p) *
          (systemSequenceRing B).obj.map q.op (b p j)
        = (systemSequenceRing B).obj.map q.op
            (∑ p : Fin k, (B.obj (op n)).obj.map g.2.op (a p) * b p j) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun p _ ↦ by rw [map_mul, hg p]
      _ = 0 := by rw [hb j, map_zero]

end SheafOfModules
