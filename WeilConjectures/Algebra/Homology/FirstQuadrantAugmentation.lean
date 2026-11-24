/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.Algebra.Homology.TotalComplex
public import Mathlib.Algebra.Homology.QuasiIso
import WeilConjectures.Algebra.Homology.FirstQuadrantTotalComparison

/-! # A columnwise criterion for a first-quadrant augmentation

## References

* Stacks Project, Homology, Tag 0133, and Cohomology, Tag 01EQ
-/

@[expose] public section

universe v u

open CategoryTheory

namespace HomologicalComplex₂

/-- A degree-zero augmentation of a first-quadrant bicomplex is a quasi-isomorphism
on total complexes if its augmentations of all resolution columns are quasi-isomorphisms. -/
theorem quasiIso_of_column_augmentation {C : Type u} [Category.{v} C] [Abelian C]
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (A : CochainComplex C ℕ) (a : A ⟶ K.X 0) (ha : a ≫ K.d 0 1 = 0)
    (b : A ⟶ K.total (ComplexShape.up ℕ))
    (hb : ∀ n : ℕ, b.f n = a.f n ≫
      K.ιTotal (ComplexShape.up ℕ) 0 n n (by simp))
    (hcol : ∀ n : ℕ, QuasiIso
      ((CochainComplex.fromSingle₀Equiv (K.flip.X n) (A.X n)).symm
        ⟨a.f n, by simpa using congrArg (fun f ↦ f.f n) ha⟩)) : QuasiIso b := by
  let S := flip (((CochainComplex.single₀ C).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj A)
  let f' : S.flip ⟶ K.flip :=
    { f := fun n ↦ (CochainComplex.fromSingle₀Equiv (K.flip.X n) (A.X n)).symm
        ⟨a.f n, by simpa using congrArg (fun f ↦ f.f n) ha⟩
      comm' := by
        intro n m h
        ext p
        cases p with
        | zero => simp [S, a.comm n m]
        | succ p =>
          apply (HomologicalComplex.isZero_single_obj_X
            (ComplexShape.up ℕ) 0 (A.X n) (p + 1) (by omega)).eq_of_src }
  let f : S ⟶ K := (flipFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f'
  have hf : ∀ n : ℕ, QuasiIso
      (((flipFunctor C (ComplexShape.up ℕ) (ComplexShape.up ℕ)).map f).f n) := by
    intro n
    exact hcol n
  let e : A ⟶ S.total (ComplexShape.up ℕ) :=
    { f := fun n ↦ S.ιTotal (ComplexShape.up ℕ) 0 n n (by simp)
      comm' := by
        intro n m h
        simp only [total_d, Preadditive.comp_add, ι_D₁, ι_D₂]
        rw [S.d₁_eq (ComplexShape.up ℕ) (by simp : (ComplexShape.up ℕ).Rel 0 1)
          n m (by simpa [Nat.add_comm] using h), S.d₂_eq (ComplexShape.up ℕ) 0 h m (by simp)]
        have hz : (S.d 0 1).f n = 0 := by
          change ((CochainComplex.single₀ C).obj (A.X n)).d 0 1 = 0
          exact HomologicalComplex.single_obj_d _ _ _ _ _
        rw [hz]
        simp [S] }
  have he' : ∀ n : ℕ, IsIso (e.f n) := by
    intro n
    let r : (S.total (ComplexShape.up ℕ)).X n ⟶ A.X n :=
      S.totalDesc (fun p q h ↦ if hp : p = 0 then by
        subst p
        exact (A.XIsoOfEq (by simpa using h)).hom
      else 0)
    refine ⟨r, ?_, ?_⟩
    · simp [e, r]
    · apply total.hom_ext
      intro p q h
      cases p with
      | zero =>
          have hq : q = n := by simpa using h
          subst q
          change S.ιTotal (ComplexShape.up ℕ) 0 n n h ≫ r ≫
              S.ιTotal (ComplexShape.up ℕ) 0 n n (by simp) =
            S.ιTotal (ComplexShape.up ℕ) 0 n n h ≫ 𝟙 _
          rw [Category.comp_id, ← Category.assoc]
          have hr : S.ιTotal (ComplexShape.up ℕ) 0 n n h ≫ r = 𝟙 (A.X n) := by
            simp [r]
          rw [hr]
          exact Category.id_comp _
      | succ p =>
          apply (HomologicalComplex.isZero_single_obj_X
            (ComplexShape.up ℕ) 0 (A.X q) (p + 1) (by omega)).eq_of_src
  have he : IsIso e := by
    have := he'
    exact HomologicalComplex.Hom.isIso_of_components e
  have hb' : e ≫ total.map f (ComplexShape.up ℕ) = b := by
    ext n
    simp [e, ιTotal_map, f, f', hb]
  have ht : QuasiIso (total.map f (ComplexShape.up ℕ)) :=
    quasiIso_totalMap_of_columns f hf
  rw [← hb']
  infer_instance

end HomologicalComplex₂
