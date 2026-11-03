/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.SequentialDerived.Helper.SequentialSemilinearDerivedDiagramsDefs
import Mathlib.Algebra.Homology.DerivedCategory.Fractions

/-! Roof data for a sequential semilinear derived diagram.

The statement is the recursive right-fraction construction used by
`sequentialSemilinearDerivedRealization`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
namespace SheafOfModules.SequentialDerived
open Helper

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  (B : ℕᵒᵖ ⥤ Sheaf J CommRingCat.{w})

/-- Recursive roofs represent a sequence of derived vertices and edge maps.

Proof source: Stacks Tags 05RT and 04VI, together with the right-fraction induction
in the proof of `lem-sf-sequential-semilinear-derived-realization`. At stage `n`,
choose a complex representing `K (n+1)`, factor the composite edge map through a
right roof, and retain the resulting denominator and numerator as the next complex
and adjacent chain map. The lower bound is irrelevant to this purely local roof
construction and is therefore absent from this helper.
(blueprint: lem-sf-sequential-semilinear-roof-data). -/
theorem sequentialSemilinearRoofData
    (K : ∀ n : ℕ, DerivedCategory (systemLevel B n))
    (k : ∀ n : ℕ, K (n + 1) ⟶ (adjacentRestriction B n).obj (K n)) :
    ∃ (L : ∀ n : ℕ, CochainComplex (systemLevel B n) ℤ)
      (a : ∀ n : ℕ, DerivedCategory.Q.obj (L n) ≅ K n)
      (b : ∀ n : ℕ,
        L (n + 1) ⟶
          ((systemRestriction B (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)).obj (L n)),
      ∀ n : ℕ,
        (a (n + 1)).hom ≫ k n ≫
            (adjacentRestriction B n).map (a n).inv ≫
            (systemRestriction B (Nat.le_succ n)).mapDerivedCategoryFactors.hom.app (L n) =
          DerivedCategory.Q.map (b n) := by
  let S : ∀ n : ℕ, Type _ := fun n ↦
    Σ L : CochainComplex (systemLevel B n) ℤ, DerivedCategory.Q.obj L ≅ K n
  let x₀ : S 0 :=
    ⟨DerivedCategory.Q.objPreimage (K 0),
      DerivedCategory.Q.objObjPreimageIso (K 0)⟩
  let step : ∀ (n : ℕ) (x : S n),
      { y : S (n + 1) //
        ∃ t : y.1 ⟶
          ((systemRestriction B (Nat.le_succ n)).mapHomologicalComplex
            (.up ℤ)).obj x.1,
          y.2.hom ≫ k n ≫ (adjacentRestriction B n).map x.2.inv ≫
              (systemRestriction B (Nat.le_succ n)).mapDerivedCategoryFactors.hom.app x.1 =
            DerivedCategory.Q.map t } := by
    intro n x
    let H : CochainComplex (systemLevel B (n + 1)) ℤ :=
      DerivedCategory.Q.objPreimage (K (n + 1))
    let h : DerivedCategory.Q.obj H ≅ K (n + 1) :=
      DerivedCategory.Q.objObjPreimageIso (K (n + 1))
    let v := (systemRestriction B (Nat.le_succ n)).mapHomologicalComplex (.up ℤ)
    let g : DerivedCategory.Q.obj H ⟶ DerivedCategory.Q.obj (v.obj x.1) :=
      h.hom ≫ k n ≫ (adjacentRestriction B n).map x.2.inv ≫
        (systemRestriction B (Nat.le_succ n)).mapDerivedCategoryFactors.hom.app x.1
    let r := DerivedCategory.right_fac g
    let L := Classical.choose r
    let h₁ := Classical.choose_spec r
    let s := Classical.choose h₁
    let h₂ := Classical.choose_spec h₁
    let hs : IsIso (DerivedCategory.Q.map s) := Classical.choose h₂
    letI : IsIso (DerivedCategory.Q.map s) := hs
    let h₃ := Classical.choose_spec h₂
    let t := Classical.choose h₃
    let ht := Classical.choose_spec h₃
    have ht' : g = inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map t := by
      simpa [s, t] using ht
    let y : S (n + 1) := ⟨L, (asIso (DerivedCategory.Q.map s)) ≪≫ h⟩
    refine ⟨y, ⟨t, ?_⟩⟩
    dsimp [y]
    calc
      (DerivedCategory.Q.map s ≫ h.hom) ≫ k n ≫
          (adjacentRestriction B n).map x.2.inv ≫
          (systemRestriction B (Nat.le_succ n)).mapDerivedCategoryFactors.hom.app x.1 =
        (asIso (DerivedCategory.Q.map s)).hom ≫ g := by
          simp [g, Category.assoc]
      _ = DerivedCategory.Q.map t := by
        calc
          (asIso (DerivedCategory.Q.map s)).hom ≫ g =
              (asIso (DerivedCategory.Q.map s)).hom ≫
                (inv (DerivedCategory.Q.map s) ≫ DerivedCategory.Q.map t) := by
            exact congrArg (fun q ↦ (asIso (DerivedCategory.Q.map s)).hom ≫ q) ht'
          _ = DerivedCategory.Q.map t := by simp
  let x : ∀ n : ℕ, S n := fun n ↦
    Nat.rec x₀ (fun n xn ↦ (step n xn).1) n
  let b : ∀ n : ℕ, (x (n + 1)).1 ⟶
      ((systemRestriction B (Nat.le_succ n)).mapHomologicalComplex
        (.up ℤ)).obj (x n).1 := fun n ↦
    Classical.choose ((step n (x n)).2)
  refine ⟨fun n ↦ (x n).1, fun n ↦ (x n).2, b, ?_⟩
  intro n
  exact Classical.choose_spec ((step n (x n)).2)

end SheafOfModules.SequentialDerived
