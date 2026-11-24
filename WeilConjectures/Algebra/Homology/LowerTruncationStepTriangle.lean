/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Successive lower truncation triangle

## References

* Stacks Project, Tag 08D4, proof of part (2); Tag 08J5
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Pretriangulated

namespace DerivedCategory

/-- The canonical transition between successive lower truncations lies in a
triangle with the shifted cohomology object. -/
theorem exists_lowerTruncationStepTriangle
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (E : DerivedCategory C) (n : ℤ) :
    ∃ (f : (Q.obj ((CochainComplex.singleFunctor C 0).obj
          ((homologyFunctor C (-n)).obj E)))⟦n⟧ ⟶
        ((TStructure.t (C := C)).truncGE (-n)).obj E)
      (h : ((TStructure.t (C := C)).truncGE (-n + 1)).obj E ⟶
        ((Q.obj ((CochainComplex.singleFunctor C 0).obj
          ((homologyFunctor C (-n)).obj E)))⟦n⟧)⟦(1 : ℤ)⟧),
      Triangle.mk f
        (((TStructure.t (C := C)).natTransTruncGEOfLE (-n) (-n + 1) (by omega)).app E) h
          ∈ distTriang (DerivedCategory C) := by
  let t := TStructure.t (C := C)
  let B := (t.truncGE (-n)).obj E
  let A := (t.truncLT (-n + 1)).obj B
  have hA₁ : A.IsLE (-n) := t.isLE_truncLT_obj B (-n + 1) (-n) (by omega)
  have hA₂ : A.IsGE (-n) := by dsimp [A, B]; infer_instance
  obtain ⟨Y, ⟨eY⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE A (-n)
  let eH : (homologyFunctor C (-n)).obj A ≅ Y :=
    (homologyFunctor C (-n)).mapIso eY ≪≫
      (singleFunctorCompHomologyFunctorIso C (-n)).app Y
  have hι := isIso_homologyFunctor_map_truncLTι_app B (-n + 1) (-n) (by omega)
  have hπ := isIso_homologyFunctor_map_truncGEπ_app E (-n) (-n) le_rfl
  let eAE : (homologyFunctor C (-n)).obj A ≅ (homologyFunctor C (-n)).obj E :=
    asIso ((homologyFunctor C (-n)).map ((t.truncLTι (-n + 1)).app B)) ≪≫
      (asIso ((homologyFunctor C (-n)).map ((t.truncGEπ (-n)).app E))).symm
  let e₁ : (Q.obj ((CochainComplex.singleFunctor C 0).obj
      ((homologyFunctor C (-n)).obj E)))⟦n⟧ ≅ A :=
    (((singleFunctors C).shiftIso n (-n) 0 (by omega)).app
      ((homologyFunctor C (-n)).obj E)) ≪≫
      (singleFunctor C (-n)).mapIso (eAE.symm ≪≫ eH) ≪≫ eY.symm
  have hmap := t.isIso_truncGE_map_truncGEπ_app (-n + 1) (-n) (by omega) E
  let e₃ : (t.truncGE (-n + 1)).obj B ≅ (t.truncGE (-n + 1)).obj E :=
    (asIso ((t.truncGE (-n + 1)).map ((t.truncGEπ (-n)).app E))).symm
  let g := (t.natTransTruncGEOfLE (-n) (-n + 1) (by omega)).app E
  have hGE : t.IsGE ((t.truncGE (-n + 1)).obj E) (-n) :=
    t.isGE_truncGE_obj E (-n + 1) (-n) (by omega)
  have hg : (t.truncGEπ (-n + 1)).app B ≫ e₃.hom = g := by
    apply t.from_truncGE_obj_ext
    dsimp [e₃, B, g]
    have hn := (t.truncGEπ (-n + 1)).naturality ((t.truncGEπ (-n)).app E)
    dsimp only [Functor.id_map] at hn
    rw [← Category.assoc, hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    simp
  refine ⟨e₁.hom ≫ (t.truncLTι (-n + 1)).app B,
    e₃.inv ≫ (t.truncGEδLT (-n + 1)).app B ≫ e₁.inv⟦(1 : ℤ)⟧', ?_⟩
  refine isomorphic_distinguished _ (t.triangleLTGE_distinguished (-n + 1) B) _ ?_
  refine Triangle.isoMk _ _ e₁ (Iso.refl _) e₃.symm (by simp) ?_ ?_
  · change g ≫ e₃.inv = 𝟙 B ≫ (t.truncGEπ (-n + 1)).app B
    rw [← hg]
    simp
  · simp

end DerivedCategory
