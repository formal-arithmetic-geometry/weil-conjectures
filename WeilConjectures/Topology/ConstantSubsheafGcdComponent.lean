/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Topology.Sheaves.Abelian
public import WeilConjectures.Topology.AbelianOpenExtensionByZero
public import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Int.GCD
import all WeilConjectures.Topology.ConstantSubsheafQuotientGluing

/-! # Bezout component on a finite intersection

## References

* Stacks Project, Tag 0A38.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace TopCat.Sheaf

/-- Realize the gcd label of a finite intersection as a component into `K`. -/
theorem constantSubsheaf_gcd_component
    (X : TopCat.{u}) (K C : Sheaf AddCommGrpCat X) (ι : K ⟶ C)
    (isoC : C ≅ (constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
      (AddCommGrpCat.of (ULift.{u} ℤ)))
    (n : ℕ) (A : Fin n → Opens X) (c : Fin n → ℕ)
    (f : ∀ i, (abelianOpenExtensionByZero (A i)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ K)
    (hvalue : ∀ i,
      (ι ≫ isoC.hom).hom.app (op (A i))
      ((f i).hom.app (op (A i)) (abelianOpenExtensionSection (A i)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (A i) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1)))) =
      (toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
      (op (A i)) (ULift.up (c i : ℤ)))
    (S : Finset (Fin n)) :
    ∃ q : (abelianOpenExtensionByZero (S.inf A)).obj
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (S.inf A)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) ⟶ K,
      (ι ≫ isoC.hom).hom.app (op (S.inf A))
      ((q).hom.app (op (S.inf A)) (abelianOpenExtensionSection (S.inf A)
      ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (S.inf A)))
        AddCommGrpCat.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) (S.inf A) le_rfl
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (S.inf A)))
        ((Functor.const (Opens ((Opens.toTopCat X).obj (S.inf A)))ᵒᵖ).obj
          (AddCommGrpCat.of (ULift.{u} ℤ)))).app
        (op ((Opens.map (S.inf A).inclusion').obj (S.inf A))) (ULift.up 1)))) =
      (toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u} ℤ)))).app
      (op (S.inf A)) (ULift.up ((S.gcd c : ℕ) : ℤ)) := by
  classical
  let Z := AddCommGrpCat.of (ULift.{u} ℤ)
  let J := Opens.grothendieckTopology X
  let η := toSheafify J ((Functor.const (Opens X)ᵒᵖ).obj Z)
  let α := ι ≫ isoC.hom
  let W := S.inf A
  let s : ∀ i, K.obj.obj (op (A i)) := fun i ↦
    (f i).hom.app (op (A i))
      (abelianOpenExtensionSection (A i)
        ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
          AddCommGrpCat.{u}).obj Z) (A i) le_rfl
        ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj (A i)))
          ((Functor.const (Opens ((Opens.toTopCat X).obj (A i)))ᵒᵖ).obj Z)).app
          (op ((Opens.map (A i).inclusion').obj (A i))) (ULift.up 1)))
  have hrestrict (i : Fin n) (h : W ≤ A i) :
      α.hom.app (op W) (K.obj.map (homOfLE h).op (s i)) =
        η.app (op W) (ULift.up (c i : ℤ)) := by
    have hα := ConcreteCategory.congr_hom (α.hom.naturality (homOfLE h).op) (s i)
    have hη := ConcreteCategory.congr_hom (η.naturality (homOfLE h).op)
      (ULift.up (c i : ℤ))
    simp only [ConcreteCategory.comp_apply] at hα hη
    rw [hα, hvalue i]
    exact hη.symm
  have hex (T : Finset (Fin n)) (hT : T ⊆ S) :
      ∃ t : K.obj.obj (op W),
        α.hom.app (op W) t = η.app (op W) (ULift.up ((T.gcd c : ℕ) : ℤ)) := by
    induction T using Finset.induction_on with
    | empty =>
      refine ⟨0, ?_⟩
      change α.hom.app (op W) 0 = η.app (op W) 0
      simp
    | @insert i T hi ih =>
      obtain ⟨t, ht⟩ := ih (fun j hj ↦ hT (Finset.mem_insert_of_mem hj))
      have hiS : i ∈ S := hT (Finset.mem_insert_self i T)
      let r := K.obj.map (homOfLE (Finset.inf_le hiS)).op (s i)
      have hr := hrestrict i (Finset.inf_le hiS)
      let a := Nat.gcdA (c i) (T.gcd c)
      let b := Nat.gcdB (c i) (T.gcd c)
      refine ⟨a • r + b • t, ?_⟩
      rw [map_add, map_zsmul, map_zsmul, hr, ht]
      erw [← map_zsmul, ← map_zsmul, ← map_add]
      congr 1
      apply ULift.ext
      change a * (c i : ℤ) + b * ((T.gcd c : ℕ) : ℤ) = (((insert i T).gcd c : ℕ) : ℤ)
      rw [Finset.gcd_insert, gcd_eq_nat_gcd]
      simpa [a, b, mul_comm] using (Nat.gcd_eq_gcd_ab (c i) (T.gcd c)).symm
  obtain ⟨t, ht⟩ := hex S (fun _ h ↦ h)
  obtain ⟨q, hq⟩ := integerExtension_of_section X K W t
  refine ⟨q, ?_⟩
  have hqt := hq W le_rfl
  rw [hqt]
  change α.hom.app (op W) (K.obj.map (𝟙 (op W)) t) = _
  rw [K.obj.map_id]
  exact ht

end TopCat.Sheaf
