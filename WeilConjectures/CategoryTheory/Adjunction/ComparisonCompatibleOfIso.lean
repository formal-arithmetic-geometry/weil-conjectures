/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapMate

/-!
# Checking the compatibility of tensor comparisons on enough objects

The compatibility `CategoryTheory.Adjunction.ComparisonCompatible` of the comparisons
`φ`, `φ'`, `m_C`, `m_D` with an isomorphism `α : N_D ⋙ F' ≅ F ⋙ N_C` is an equality of
components of natural transformations of bifunctors. It therefore suffices to check it on
objects to which every object is isomorphic
(`CategoryTheory.Adjunction.comparisonCompatible_of_iso`), for instance on the images of K-flat
complexes in a derived category.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open _root_.CategoryTheory.Functor

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  {F : D ⥤ C} {F' : D' ⥤ C'} {N_D : D ⥤ D'} {N_C : C ⥤ C'} (α : N_D ⋙ F' ≅ F ⋙ N_C)
  {T_C : C ⥤ C ⥤ C} {T_D : D ⥤ D ⥤ D} {T_C' : C' ⥤ C' ⥤ C'} {T_D' : D' ⥤ D' ⥤ D'}
  (φ : (postcompose₂.obj F).obj T_D ⟶ (((whiskeringLeft₂ C).obj F).obj F).obj T_C)
  (φ' : (postcompose₂.obj F').obj T_D' ⟶ (((whiskeringLeft₂ C').obj F').obj F').obj T_C')
  (m_C : (postcompose₂.obj N_C).obj T_C ≅ (((whiskeringLeft₂ C').obj N_C).obj N_C).obj T_C')
  (m_D : (postcompose₂.obj N_D).obj T_D ≅ (((whiskeringLeft₂ D').obj N_D).obj N_D).obj T_D')


/-- Composition of the maps induced by a bifunctor in both variables. -/
@[reassoc]
lemma bimap_comp_bimap (T : C' ⥤ C' ⥤ C') {x x' x'' y y' y'' : C'} (f : x ⟶ x') (f' : x' ⟶ x'')
    (g : y ⟶ y') (g' : y' ⟶ y'') :
    (T.map f).app y ≫ (T.obj x').map g ≫ (T.map f').app y' ≫ (T.obj x'').map g' =
      (T.map (f ≫ f')).app y ≫ (T.obj x'').map (g ≫ g') := by
  have h := (T.map f').naturality g
  simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [reassoc_of% h]

/-- The compatibility `ComparisonCompatible` holds as soon as it holds on a family of objects to
which every object is isomorphic: both sides are natural in the two variables. -/
lemma comparisonCompatible_of_iso (S : D → Prop) (hS : ∀ a, ∃ a', S a' ∧ Nonempty (a ≅ a'))
    (h : ∀ a b, S a → S b →
      N_C.map ((φ.app a).app b) ≫ (m_C.hom.app (F.obj a)).app (F.obj b) =
        α.inv.app ((T_D.obj a).obj b) ≫ F'.map ((m_D.hom.app a).app b) ≫
          (φ'.app (N_D.obj a)).app (N_D.obj b) ≫ (T_C'.map (α.hom.app a)).app _ ≫
            (T_C'.obj _).map (α.hom.app b)) :
    ComparisonCompatible α φ φ' m_C m_D := by
  intro a b
  obtain ⟨a', ha', ⟨ea⟩⟩ := hS a
  obtain ⟨b', hb', ⟨eb⟩⟩ := hS b
  have H := h a' b' ha' hb'
  -- the transport of both sides along `ea` and `eb`
  let t : (T_D.obj a).obj b ⟶ (T_D.obj a').obj b' :=
    (T_D.map ea.hom).app b ≫ (T_D.obj a').map eb.hom
  have hφ₀ : F.map t ≫ (φ.app a').app b' = (φ.app a).app b ≫
      (T_C.map (F.map ea.hom)).app (F.obj b) ≫ (T_C.obj (F.obj a')).map (F.map eb.hom) := by
    have h₁ := NatTrans.congr_app (φ.naturality ea.hom) b
    have h₂ := (φ.app a').naturality eb.hom
    dsimp at h₁ h₂
    simp only [t, Functor.map_comp, Category.assoc]
    rw [h₂, reassoc_of% h₁]
  have hφ : N_C.map (F.map t) ≫ N_C.map ((φ.app a').app b') = N_C.map ((φ.app a).app b) ≫
      N_C.map ((T_C.map (F.map ea.hom)).app (F.obj b) ≫
        (T_C.obj (F.obj a')).map (F.map eb.hom)) := by
    rw [← N_C.map_comp, hφ₀, N_C.map_comp]
  have hm : N_C.map ((T_C.map (F.map ea.hom)).app (F.obj b) ≫
        (T_C.obj (F.obj a')).map (F.map eb.hom)) ≫ (m_C.hom.app (F.obj a')).app (F.obj b') =
      (m_C.hom.app (F.obj a)).app (F.obj b) ≫ (T_C'.map (N_C.map (F.map ea.hom))).app _ ≫
        (T_C'.obj _).map (N_C.map (F.map eb.hom)) := by
    have h₁ := NatTrans.congr_app (m_C.hom.naturality (F.map ea.hom)) (F.obj b)
    have h₂ := (m_C.hom.app (F.obj a')).naturality (F.map eb.hom)
    dsimp at h₁ h₂
    rw [Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁]
  have hα : α.inv.app ((T_D.obj a).obj b) ≫ F'.map (N_D.map t) =
      N_C.map (F.map t) ≫ α.inv.app ((T_D.obj a').obj b') := (α.inv.naturality t).symm
  have hmD : N_D.map t ≫ (m_D.hom.app a').app b' =
      (m_D.hom.app a).app b ≫ (T_D'.map (N_D.map ea.hom)).app _ ≫
        (T_D'.obj _).map (N_D.map eb.hom) := by
    have h₁ := NatTrans.congr_app (m_D.hom.naturality ea.hom) b
    have h₂ := (m_D.hom.app a').naturality eb.hom
    dsimp at h₁ h₂
    simp only [t, Functor.map_comp, Category.assoc]
    rw [h₂, reassoc_of% h₁]
  have hφ' : F'.map ((T_D'.map (N_D.map ea.hom)).app (N_D.obj b) ≫
        (T_D'.obj (N_D.obj a')).map (N_D.map eb.hom)) ≫ (φ'.app (N_D.obj a')).app (N_D.obj b') =
      (φ'.app (N_D.obj a)).app (N_D.obj b) ≫ (T_C'.map (F'.map (N_D.map ea.hom))).app _ ≫
        (T_C'.obj _).map (F'.map (N_D.map eb.hom)) := by
    have h₁ := NatTrans.congr_app (φ'.naturality (N_D.map ea.hom)) (N_D.obj b)
    have h₂ := (φ'.app (N_D.obj a')).naturality (N_D.map eb.hom)
    dsimp at h₁ h₂
    rw [Functor.map_comp, Category.assoc, h₂, reassoc_of% h₁]
  have hαa : α.hom.app a ≫ N_C.map (F.map ea.hom) = F'.map (N_D.map ea.hom) ≫ α.hom.app a' :=
    (α.hom.naturality ea.hom).symm
  have hαb : α.hom.app b ≫ N_C.map (F.map eb.hom) = F'.map (N_D.map eb.hom) ≫ α.hom.app b' :=
    (α.hom.naturality eb.hom).symm
  rw [← cancel_mono ((T_C'.map (N_C.map (F.map ea.hom))).app _ ≫
    (T_C'.obj _).map (N_C.map (F.map eb.hom)))]
  calc _ = N_C.map (F.map t) ≫ N_C.map ((φ.app a').app b') ≫
        (m_C.hom.app (F.obj a')).app (F.obj b') := by
        rw [Category.assoc, ← hm, reassoc_of% hφ]
    _ = N_C.map (F.map t) ≫ α.inv.app ((T_D.obj a').obj b') ≫
        F'.map ((m_D.hom.app a').app b') ≫
        (φ'.app (N_D.obj a')).app (N_D.obj b') ≫ (T_C'.map (α.hom.app a')).app _ ≫
          (T_C'.obj _).map (α.hom.app b') := by rw [H]
    _ = α.inv.app ((T_D.obj a).obj b) ≫ F'.map (N_D.map t) ≫
        F'.map ((m_D.hom.app a').app b') ≫
        (φ'.app (N_D.obj a')).app (N_D.obj b') ≫ (T_C'.map (α.hom.app a')).app _ ≫
          (T_C'.obj _).map (α.hom.app b') := by rw [reassoc_of% hα]
    _ = α.inv.app ((T_D.obj a).obj b) ≫ F'.map ((m_D.hom.app a).app b) ≫
        (φ'.app (N_D.obj a)).app (N_D.obj b) ≫ (T_C'.map (F'.map (N_D.map ea.hom))).app _ ≫
        (T_C'.obj _).map (F'.map (N_D.map eb.hom)) ≫ (T_C'.map (α.hom.app a')).app _ ≫
          (T_C'.obj _).map (α.hom.app b') := by
        rw [← F'.map_comp_assoc, hmD, F'.map_comp_assoc, reassoc_of% hφ']
    _ = _ := by
        rw [bimap_comp_bimap, ← hαa, ← hαb, ← bimap_comp_bimap]
        simp only [Category.assoc]
        rfl

end CategoryTheory.Adjunction
