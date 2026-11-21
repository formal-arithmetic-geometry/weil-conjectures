/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Module.Projective
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.RingTheory.Finiteness.Defs
import WeilConjectures.Algebra.Homology.FiniteProjectiveModuleColimitDescent
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.Data.Int.Interval

/-! # Descent of bounded graded finite projective modules

## References

* Stacks Project, More on Algebra, Tag 0BC7, proof of (1)
* Stacks Project, Algebra, Tags 05N7 and 00NX
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace ModuleCat

private theorem finite_extendScalars {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} R) [Module.Finite R M] :
    Module.Finite S ((extendScalars f).obj M) := by
  let := f.toAlgebra
  change Module.Finite S (TensorProduct R S M)
  infer_instance

private theorem projective_extendScalars {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} R) [Module.Projective R M] :
    Module.Projective S ((extendScalars f).obj M) := by
  let := f.toAlgebra
  change Module.Projective S (TensorProduct R S M)
  infer_instance

private theorem common_stage {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    [Nonempty I] (s : Finset I) : ∃ j, ∀ i ∈ s, i ≤ j := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨Classical.arbitrary I, by simp⟩
  | @insert i s hi ih =>
    obtain ⟨j, hj⟩ := ih
    obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
    exact ⟨k, by simpa using And.intro hik (fun x hx ↦ (hj x hx).trans hjk)⟩

private noncomputable def model_baseChange_iso
    {I : Type u} [Preorder I] (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    {i j : I} (hij : i ≤ j) (M : ModuleCat.{u} (F.obj i)) :
    (extendScalars (colimit.ι F j).hom).obj
      ((extendScalars (F.map (homOfLE hij)).hom).obj M) ≅
        (extendScalars (colimit.ι F i).hom).obj M := by
  have h : (colimit.ι F j).hom.comp (F.map (homOfLE hij)).hom =
      (colimit.ι F i).hom := by
    exact congrArg CommRingCat.Hom.hom (colimit.w F (homOfLE hij))
  exact (extendScalarsComp (F.map (homOfLE hij)).hom (colimit.ι F j).hom).symm.app M ≪≫
    (eqToIso (congrArg (fun f ↦ (extendScalars f).obj M) h))

/-- A bounded graded family of finite projective modules descends with the same support bounds. -/
theorem exists_finite_projective_graded_model_of_directed_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (F : I ⥤ CommRingCat.{u}) [HasColimit F]
    (X : ℤ → ModuleCat.{u} (colimit F : CommRingCat.{u})) (a b : ℤ)
    (hzero : ∀ n : ℤ, n < a ∨ b < n → IsZero (X n))
    (hfinite : ∀ n : ℤ, Module.Finite (colimit F : CommRingCat.{u}) (X n))
    (hprojective : ∀ n : ℤ, Module.Projective (colimit F : CommRingCat.{u}) (X n)) :
    ∃ (i : I) (M : ℤ → ModuleCat.{u} (F.obj i)),
      (∀ n : ℤ, n < a ∨ b < n → IsZero (M n)) ∧
      (∀ n : ℤ, Module.Finite (F.obj i) (M n)) ∧
      (∀ n : ℤ, Module.Projective (F.obj i) (M n)) ∧
      Nonempty (∀ n : ℤ, (extendScalars (colimit.ι F i).hom).obj (M n) ≅ X n) := by
  classical
  have hm (n : ℤ) := exists_finite_projective_module_model_of_directed_colimit
    F (X n) (hfinite n) (hprojective n)
  choose i N hNfinite hNprojective e using hm
  let s := Finset.Icc a b
  obtain ⟨j, hj⟩ := common_stage (s.image i)
  have hij (n : ℤ) (hn : n ∈ s) : i n ≤ j := hj (i n) (Finset.mem_image.mpr ⟨n, hn, rfl⟩)
  let M : ℤ → ModuleCat.{u} (F.obj j) := fun n ↦
    if hn : n ∈ s then (extendScalars (F.map (homOfLE (hij n hn))).hom).obj (N n)
    else ModuleCat.of (F.obj j) PUnit.{u + 1}
  refine ⟨j, M, ?_, ?_, ?_, ⟨?_⟩⟩
  · intro n hn
    have hs : n ∉ s := by
      simp only [s, Finset.mem_Icc] at *
      omega
    dsimp [M]
    rw [dite_eq_right hs]
    exact isZero_of_subsingleton _
  · intro n
    by_cases hn : n ∈ s
    · rw [show M n = _ from dite_eq_left hn]
      let := hNfinite n
      exact finite_extendScalars (F.map (homOfLE (hij n hn))).hom (N n)
    · rw [show M n = _ from dite_eq_right hn]
      infer_instance
  · intro n
    by_cases hn : n ∈ s
    · rw [show M n = _ from dite_eq_left hn]
      let := hNprojective n
      exact projective_extendScalars (F.map (homOfLE (hij n hn))).hom (N n)
    · rw [show M n = _ from dite_eq_right hn]
      infer_instance
  · intro n
    dsimp [M]
    split_ifs with hn
    · exact model_baseChange_iso F (hij n hn) (N n) ≪≫ (e n).some
    · have hz : IsZero (ModuleCat.of (F.obj j) PUnit.{u + 1}) := isZero_of_subsingleton _
      exact ((extendScalars (colimit.ι F j).hom).map_isZero hz).iso
        (hzero n (by
          simp only [s, Finset.mem_Icc] at hn
          omega))

end ModuleCat
