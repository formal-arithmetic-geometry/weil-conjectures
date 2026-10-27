/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q114
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Scalar-unit normalized adjunction squares

Source: Bhatt–Scholze, Remark 6.8.15 (ambient setting); Stacks Project, Tag 0037
(adjunct formulas); the scalar-adjunction calculation extracted from the realization
comparisons (blueprint: lem-weil-pbc-scalar-normalized-adjunction-square).
-/

@[expose] public section

set_option autoImplicit false

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

namespace CategoryTheory.Adjunction

/-- Scalar-unit normalized comparison squares preserve the horizontal adjunctions,
including the explicit counit transposes, unit transpose, and mates correspondence.

Source: Bhatt–Scholze, Remark 6.8.15 (ambient adjunction setting), and Stacks Project,
Tag 0037 (adjunct formulas). The square calculation is an agent extraction from the
realization adjoint comparisons
(blueprint: lem-weil-pbc-scalar-normalized-adjunction-square).

Proof:
1. Use the Hom bijections and their unit/counit formulas from
   lem-weil-pbc-adjunction-of-natural-bijection. Fullness and the two containment
   hypotheses restrict the unprimed adjunction to the full subcategories.
2. At M in D₀, expand the vertical transpose of the composite counit comparison.
   Apply the first normalization at QM, then naturality of b inverse at β_M, obtaining
   P(j_C) followed by P(r_C β_M), b inverse at Q'F_DM, and r_D(ε').
3. Apply the ambient counit compatibility at Z = F_DM, then the second normalization
   at M. Naturality of ε identifies the result with ε_M followed by j_D,M.
   Naturality of j_D gives the same transpose for F_D(ε_M).
4. Injectivity of the vertical Hom bijection gives the counit comparison. Cancel
   the invertible α_QM to obtain the transpose characterization of β_M.
5. For N in C₀ take the inverse primed horizontal transpose of the unit comparison.
   Naturality of ε', step 4 at PN, and naturality of α at η_N reduce it to α_N
   inverse followed by F_D of the unprimed left triangle, followed by α_N.
   It is identity; the Hom bijection therefore gives the asserted primed unit.
6. Step 4 identifies β with the mate of α inverse in the convention of
   def-weil-pbc-adjunction-mate, implemented by Mathlib's mateEquiv. Only Hom
   bijections and specified isomorphisms are cancelled.
-/
theorem scalarNormalizedAdjunctionSquare
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    {P : C ⥤ D} {Q : D ⥤ C} {P' : C' ⥤ D'} {Q' : D' ⥤ C'}
    (adj : P ⊣ Q) (adj' : P' ⊣ Q')
    {FC : C ⥤ C'} {rC : C' ⥤ C} {FD : D ⥤ D'} {rD : D' ⥤ D}
    (scalarC : FC ⊣ rC) (scalarD : FD ⊣ rD)
    (C₀ : ObjectProperty C) (D₀ : ObjectProperty D)
    (hP : ∀ N : C₀.FullSubcategory, D₀ (P.obj N.obj))
    (hQ : ∀ M : D₀.FullSubcategory, C₀ (Q.obj M.obj))
    (b : P' ⋙ rD ≅ rC ⋙ P) (d : Q' ⋙ rC ≅ rD ⋙ Q)
    (α : C₀.ι ⋙ P ⋙ FD ≅ C₀.ι ⋙ FC ⋙ P')
    (β : D₀.ι ⋙ Q ⋙ FC ⟶ D₀.ι ⋙ FD ⋙ Q')
    (hα : ∀ N : C₀.FullSubcategory,
      scalarD.unit.app (P.obj N.obj) ≫ rD.map (α.hom.app N) =
        P.map (scalarC.unit.app N.obj) ≫ b.inv.app (FC.obj N.obj))
    (hβ : ∀ M : D₀.FullSubcategory,
      scalarC.unit.app (Q.obj M.obj) ≫ rC.map (β.app M) =
        Q.map (scalarD.unit.app M.obj) ≫ d.inv.app (FD.obj M.obj))
    (hε : ∀ Z : D',
      b.inv.app (Q'.obj Z) ≫ rD.map (adj'.counit.app Z) =
        P.map (d.hom.app Z) ≫ adj.counit.app (rD.obj Z)) :
    (∀ M : D₀.FullSubcategory,
      (scalarD.unit.app (P.obj (Q.obj M.obj)) ≫
          rD.map (α.hom.app ⟨Q.obj M.obj, hQ M⟩ ≫
            P'.map (β.app M) ≫ adj'.counit.app (FD.obj M.obj)) =
        adj.counit.app M.obj ≫ scalarD.unit.app M.obj) ∧
      (adj.counit.app M.obj ≫ scalarD.unit.app M.obj =
        scalarD.unit.app (P.obj (Q.obj M.obj)) ≫ rD.map (FD.map (adj.counit.app M.obj))) ∧
      (FD.map (adj.counit.app M.obj) =
        α.hom.app ⟨Q.obj M.obj, hQ M⟩ ≫ P'.map (β.app M) ≫
          adj'.counit.app (FD.obj M.obj))) ∧
    (∀ N : C₀.FullSubcategory,
      ((adj'.homEquiv (FC.obj N.obj) (P'.obj (FC.obj N.obj))).symm
          (FC.map (adj.unit.app N.obj) ≫ β.app ⟨P.obj N.obj, hP N⟩ ≫
            Q'.map (α.hom.app N)) = 𝟙 (P'.obj (FC.obj N.obj))) ∧
      (FC.map (adj.unit.app N.obj) ≫ β.app ⟨P.obj N.obj, hP N⟩ ≫
          Q'.map (α.hom.app N) = adj'.unit.app (FC.obj N.obj))) ∧
    (mateEquiv
      (G := C₀.ι ⋙ FC) (H := D₀.ι ⋙ FD)
      (adj.restrictFullyFaithful C₀.fullyFaithfulι D₀.fullyFaithfulι
        (L := D₀.lift (C₀.ι ⋙ P) hP) (R := C₀.lift (D₀.ι ⋙ Q) hQ)
        (Iso.refl _) (Iso.refl _)) adj'
      (TwoSquare.mk _ _ _ _ α.inv)).natTrans = β := by
  have ht (M : D₀.FullSubcategory) :
      scalarD.unit.app (P.obj (Q.obj M.obj)) ≫
          rD.map (α.hom.app ⟨Q.obj M.obj, hQ M⟩ ≫
            P'.map (β.app M) ≫ adj'.counit.app (FD.obj M.obj)) =
        adj.counit.app M.obj ≫ scalarD.unit.app M.obj := by
    simp only [Functor.map_comp]
    rw [← Category.assoc, hα ⟨Q.obj M.obj, hQ M⟩]
    have hb := b.inv.naturality (β.app M)
    change P.map (rC.map (β.app M)) ≫ b.inv.app (Q'.obj (FD.obj M.obj)) =
      b.inv.app (FC.obj (Q.obj M.obj)) ≫ rD.map (P'.map (β.app M)) at hb
    rw [Category.assoc, ← reassoc_of% hb, ← Category.assoc, ← P.map_comp, hβ]
    simp only [P.map_comp, Category.assoc]
    rw [hε, ← P.map_comp_assoc (d.inv.app _) (d.hom.app _),
      d.inv_hom_id_app, P.map_id, Category.id_comp]
    exact adj.counit.naturality (scalarD.unit.app M.obj)
  have hn (M : D₀.FullSubcategory) :
      adj.counit.app M.obj ≫ scalarD.unit.app M.obj =
        scalarD.unit.app (P.obj (Q.obj M.obj)) ≫
          rD.map (FD.map (adj.counit.app M.obj)) :=
    scalarD.unit.naturality (adj.counit.app M.obj)
  have hc (M : D₀.FullSubcategory) :
      FD.map (adj.counit.app M.obj) =
        α.hom.app ⟨Q.obj M.obj, hQ M⟩ ≫ P'.map (β.app M) ≫
          adj'.counit.app (FD.obj M.obj) := by
    apply (scalarD.homEquiv _ _).injective
    exact (hn M).symm.trans (ht M).symm
  let a := adj.restrictFullyFaithful C₀.fullyFaithfulι D₀.fullyFaithfulι
    (L := D₀.lift (C₀.ι ⋙ P) hP) (R := C₀.lift (D₀.ι ⋙ Q) hQ)
    (Iso.refl _) (Iso.refl _)
  let θ : TwoSquare (C₀.ι ⋙ FC) (D₀.lift (C₀.ι ⋙ P) hP) P' (D₀.ι ⋙ FD) :=
    TwoSquare.mk _ _ _ _ α.inv
  have hm : (mateEquiv (G := C₀.ι ⋙ FC) (H := D₀.ι ⋙ FD) a adj' θ).natTrans = β := by
    ext M
    apply (adj'.homEquiv _ _).symm.injective
    rw [homEquiv_symm_apply, homEquiv_symm_apply]
    have he := mateEquiv_counit a adj' θ M
    change P'.map _ ≫ adj'.counit.app _ =
      α.inv.app ⟨Q.obj M.obj, hQ M⟩ ≫ FD.map (D₀.ι.map (a.counit.app M)) at he
    have ha : D₀.ι.map (a.counit.app M) = adj.counit.app M.obj := by
      simpa using (adj.map_restrictFullyFaithful_counit_app
        C₀.fullyFaithfulι D₀.fullyFaithfulι
        (L := D₀.lift (C₀.ι ⋙ P) hP) (R := C₀.lift (D₀.ι ⋙ Q) hQ)
        (Iso.refl _) (Iso.refl _) M)
    rw [ha, hc, Iso.inv_hom_id_app_assoc] at he
    exact he
  have hu (N : C₀.FullSubcategory) :
      FC.map (adj.unit.app N.obj) ≫ β.app ⟨P.obj N.obj, hP N⟩ ≫
        Q'.map (α.hom.app N) = adj'.unit.app (FC.obj N.obj) := by
    have he := unit_mateEquiv a adj' θ N
    change FC.map (C₀.ι.map (a.unit.app N)) ≫
      (mateEquiv a adj' θ).natTrans.app ⟨P.obj N.obj, hP N⟩ =
      adj'.unit.app (FC.obj N.obj) ≫ Q'.map (α.inv.app N) at he
    have ha : C₀.ι.map (a.unit.app N) = adj.unit.app N.obj := by
      simpa using (adj.map_restrictFullyFaithful_unit_app
        C₀.fullyFaithfulι D₀.fullyFaithfulι
        (L := D₀.lift (C₀.ι ⋙ P) hP) (R := C₀.lift (D₀.ι ⋙ Q) hQ)
        (Iso.refl _) (Iso.refl _) N)
    rw [ha, hm] at he
    rw [← Category.assoc, he, Category.assoc, ← Q'.map_comp]
    simp
  refine ⟨fun M ↦ ⟨ht M, hn M, hc M⟩, fun N ↦ ⟨?_, hu N⟩, hm⟩
  rw [hu]
  simp [homEquiv_symm_apply]

end CategoryTheory.Adjunction
