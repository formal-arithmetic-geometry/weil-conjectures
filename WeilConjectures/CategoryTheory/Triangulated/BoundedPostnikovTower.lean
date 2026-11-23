/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Finite ordered Postnikov towers

The double truncation `t.truncGELE q q` is Mathlib's existing composite
`t.truncLE q ⋙ t.truncGE q`. Its value shifted by `q` is the heart object `H_t^q(K)`.
No global boundedness or nondegeneracy of the t-structure is assumed.

## References

* BBD, Faisceaux pervers, Propositions 1.3.3 and 1.3.5, Theorem 1.3.6 and its derived-category
  example, pp. 29-32.
-/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open ZeroObject

namespace CategoryTheory.Triangulated.TStructure

/-- An object with t-amplitude `[a, a + n - 1]` has an ordered Postnikov tower with
exactly `n` triangles and with its own cohomology objects as the successive factors.
The `n + 1` vertices are the upper truncations, up to isomorphism, starting at zero
and ending at the given object. For `n = 0` these endpoints identify the object with zero.
Source: BBD, Faisceaux pervers, 1.3.3-1.3.6, pp. 29-32, and 1.3.13, pp. 34-35. -/
theorem exists_bounded_postnikov_tower
    {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ m : ℤ, (shiftFunctor C m).Additive] [Pretriangulated C] [IsTriangulated C]
    (t : TStructure C) (a : ℤ) (n : ℕ) (K : C)
    [t.IsGE K a] [t.IsLE K (a + (n : ℤ) - 1)] :
    (∀ q : ℤ, t.heart (((t.truncGELE q q).obj K)⟦q⟧)) ∧
      ∃ L : Fin (n + 1) → C,
        Nonempty (L 0 ≅ 0) ∧ Nonempty (L (Fin.last n) ≅ K) ∧
        (∀ j : Fin (n + 1), Nonempty (L j ≅ (t.truncLE (a + (j : ℤ) - 1)).obj K)) ∧
        ∃ (f : ∀ j : Fin n, L j.castSucc ⟶ L j.succ)
          (g : ∀ j : Fin n, L j.succ ⟶
            (((t.truncGELE (a + (j : ℤ)) (a + (j : ℤ))).obj K)⟦a + (j : ℤ)⟧)⟦
              -(a + (j : ℤ))⟧)
          (δ : ∀ j : Fin n,
            (((t.truncGELE (a + (j : ℤ)) (a + (j : ℤ))).obj K)⟦a + (j : ℤ)⟧)⟦
              -(a + (j : ℤ))⟧ ⟶ (L j.castSucc)⟦(1 : ℤ)⟧),
          ∀ j : Fin n, Triangle.mk (f j) (g j) (δ j) ∈ distTriang C := by
  classical
  constructor
  · intro q
    apply (t.mem_heart_iff _).2
    exact ⟨t.isLE_shift _ q q 0 (by omega), t.isGE_shift _ q q 0 (by omega)⟩
  · let L : Fin (n + 1) → C := fun j ↦ (t.truncLT (a + (j : ℤ))).obj K
    refine ⟨L, ?_, ?_, ?_, ?_⟩
    · simpa [L] using (Nonempty.intro (t.isZero_truncLT_obj_of_isGE a K).isoZero)
    · exact ⟨((t.truncLEIsoTruncLT (a + (n : ℤ) - 1) (a + (n : ℤ))
        (by omega)).app K).symm ≪≫ asIso ((t.truncLEι _).app K)⟩
    · intro j
      exact ⟨((t.truncLEIsoTruncLT (a + (j : ℤ) - 1) (a + (j : ℤ))
        (by omega)).app K).symm⟩
    · have layer (j : Fin n) :
          ∃ (f : L j.castSucc ⟶ L j.succ)
            (g : L j.succ ⟶
              (((t.truncGELE (a + (j : ℤ)) (a + (j : ℤ))).obj K)⟦a + (j : ℤ)⟧)⟦
                -(a + (j : ℤ))⟧)
            (δ : (((t.truncGELE (a + (j : ℤ)) (a + (j : ℤ))).obj K)⟦
                a + (j : ℤ)⟧)⟦-(a + (j : ℤ))⟧ ⟶ (L j.castSucc)⟦(1 : ℤ)⟧),
            Triangle.mk f g δ ∈ distTriang C := by
        let q := a + (j : ℤ)
        let T := (t.triangleLTLTGELT q (q + 1) (by omega)).obj K
        let e : T.obj₃ ≅ (((t.truncGELE q q).obj K)⟦q⟧)⟦-q⟧ :=
          ((t.truncGELEIsoTruncGELT q q (q + 1) rfl).app K).symm ≪≫
            ((shiftFunctorCompIsoId C q (-q) (by omega)).app _).symm
        have hT := t.triangleLTLTGELT_distinguished q (q + 1) (by omega) K
        have h : Triangle.mk T.mor₁ (T.mor₂ ≫ e.hom) (e.inv ≫ T.mor₃) ∈
            distTriang C := by
          refine isomorphic_distinguished T hT _ ?_
          exact Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) e.symm
            (by simp) (by simp) (by simp)
        have hsucc : a + (j.succ : ℤ) = q + 1 := by
          simp [q, add_assoc]
        have hcast : a + (j.castSucc : ℤ) = q := rfl
        dsimp only [L]
        rw [hcast, hsucc]
        exact ⟨T.mor₁, T.mor₂ ≫ e.hom, e.inv ≫ T.mor₃, h⟩
      choose f g δ h using layer
      exact ⟨f, g, δ, h⟩

end CategoryTheory.Triangulated.TStructure

namespace DerivedCategory

/-- For the standard t-structure, `H_t^q(K)` is the ordinary cohomology object of
this same `K` placed in degree zero. Shifting this isomorphism by `-q` identifies
the factors in `exists_bounded_postnikov_tower` with `H^q(K)[0][-q]`.
Source: BBD, Faisceaux pervers, the example after 1.3.6, p. 31; Stacks Project, Tag 08J5. -/
theorem bounded_postnikov_cohomology_iso
    {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
    (K : DerivedCategory C) (q : ℤ) :
    Nonempty ((((TStructure.t (C := C)).truncGELE q q).obj K)⟦q⟧ ≅
      (singleFunctor C 0).obj ((homologyFunctor C q).obj K)) := by
  let t := TStructure.t (C := C)
  let L := (t.truncLE q).obj K
  let M := (t.truncGE q).obj L
  have : M.IsLE q := inferInstanceAs (t.IsLE ((t.truncGE q).obj L) q)
  have : M.IsGE q := inferInstanceAs (t.IsGE ((t.truncGE q).obj L) q)
  obtain ⟨Y, ⟨e⟩⟩ := exists_iso_singleFunctor_obj_of_isGE_of_isLE M q
  let H := homologyFunctor C q
  have : IsIso (H.map ((t.truncLTι (q + 1)).app K)) :=
    isIso_homologyFunctor_map_truncLTι_app K (q + 1) q (by omega)
  have : IsIso (H.map ((t.truncGEπ q).app L)) :=
    isIso_homologyFunctor_map_truncGEπ_app L q q le_rfl
  let eL : H.obj L ≅ H.obj K :=
    H.mapIso ((t.truncLEIsoTruncLT q (q + 1) rfl).app K) ≪≫
      asIso (H.map ((t.truncLTι (q + 1)).app K))
  let eY : Y ≅ H.obj K :=
    ((singleFunctorCompHomologyFunctorIso C q).app Y).symm ≪≫
      (H.mapIso e).symm ≪≫ (asIso (H.map ((t.truncGEπ q).app L))).symm ≪≫ eL
  exact ⟨(shiftFunctor _ q).mapIso e ≪≫
    ((singleFunctors C).shiftIso q 0 q (by omega)).app Y ≪≫
      (singleFunctor C 0).mapIso eY⟩

end DerivedCategory
