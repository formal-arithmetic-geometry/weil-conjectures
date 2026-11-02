/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.ProjectionMap
public import Mathlib.CategoryTheory.Monoidal.Functor
public import Mathlib.CategoryTheory.Adjunction.Mates

/-!
# The unit projection map of an adjunction with an oplax monoidal left adjoint

Let `adj : F ⊣ G` be an adjunction whose left adjoint `F : D ⥤ C` is oplax monoidal. The
*unit projection map* `K ⊗ G 𝟙 ⟶ G (F K)` (`CategoryTheory.Adjunction.oplaxUnitProjection`) is the
transpose of `F (K ⊗ G 𝟙) ⟶ F K ⊗ F G 𝟙 ⟶ F K ⊗ 𝟙 ≅ F K`. For the derived extension of scalars
`Ψ ⊣ Res` along `Λ ⟶ Λ'` it is the comparison `K ⊗ᴸ Res Λ'_X ⟶ Res Ψ K`.

We show that it is an isomorphism at the unit when `η F` is one
(`CategoryTheory.Adjunction.isIso_oplaxUnitProjection_tensorUnit`), and that it is compatible with
functors `N_D`, `N_C` commuting with the left adjoints through an isomorphism `α` compatible with
the comonoidal structures
(`CategoryTheory.Adjunction.map_oplaxUnitProjection_comp_mateEquiv`), and we
record how mates of squares are conjugated by natural transformations of the horizontal
functors (`CategoryTheory.Adjunction.homEquiv_comp_map_comp_counit_conj`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.OplaxMonoidal

namespace Adjunction

section UnitProjection

variable {C D : Type*} [Category* C] [Category* D] [MonoidalCategory C] [MonoidalCategory D]
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]

/-- The *unit projection map* `K ⊗ G 𝟙 ⟶ G (F K)` of an adjunction `F ⊣ G` with an oplax monoidal
left adjoint: the transpose of `F (K ⊗ G 𝟙) ⟶ F K ⊗ F (G 𝟙) ⟶ F K ⊗ 𝟙 ≅ F K`. -/
noncomputable def oplaxUnitProjection (K : D) : K ⊗ G.obj (𝟙_ C) ⟶ G.obj (F.obj K) :=
  adj.homEquiv _ _ (δ F K (G.obj (𝟙_ C)) ≫ F.obj K ◁ adj.counit.app (𝟙_ C) ≫ (ρ_ (F.obj K)).hom)

lemma homEquiv_symm_oplaxUnitProjection (K : D) :
    (adj.homEquiv _ _).symm (adj.oplaxUnitProjection K) =
      δ F K (G.obj (𝟙_ C)) ≫ F.obj K ◁ adj.counit.app (𝟙_ C) ≫ (ρ_ (F.obj K)).hom :=
  Equiv.symm_apply_apply _ _

@[reassoc]
lemma map_oplaxUnitProjection_comp_counit (K : D) :
    F.map (adj.oplaxUnitProjection K) ≫ adj.counit.app (F.obj K) =
      δ F K (G.obj (𝟙_ C)) ≫ F.obj K ◁ adj.counit.app (𝟙_ C) ≫ (ρ_ (F.obj K)).hom := by
  simpa [homEquiv_counit] using adj.homEquiv_symm_oplaxUnitProjection K

/-- The unit projection map is natural. -/
@[reassoc]
lemma oplaxUnitProjection_naturality {K K' : D} (f : K ⟶ K') :
    f ▷ G.obj (𝟙_ C) ≫ adj.oplaxUnitProjection K' =
      adj.oplaxUnitProjection K ≫ G.map (F.map f) := by
  apply (adj.homEquiv _ _).symm.injective
  rw [homEquiv_naturality_left_symm, homEquiv_naturality_right_symm,
    homEquiv_symm_oplaxUnitProjection, homEquiv_symm_oplaxUnitProjection, ← δ_natural_left_assoc,
    ← whisker_exchange_assoc]
  simp only [Functor.id_obj, rightUnitor_naturality, Category.assoc]

/-- At the unit, the unit projection map `𝟙 ⊗ G 𝟙 ⟶ G (F 𝟙)` is the left unitor followed by `G`
of the isomorphism `𝟙 ≅ F 𝟙` given by `η F`, when `η F` is an isomorphism. -/
lemma oplaxUnitProjection_tensorUnit [IsIso (η F)] :
    adj.oplaxUnitProjection (𝟙_ D) = (λ_ _).hom ≫
      G.map ((λ_ (𝟙_ C)).inv ≫ inv (η F) ▷ 𝟙_ C ≫ (ρ_ (F.obj (𝟙_ D))).hom) := by
  apply (adj.homEquiv _ _).symm.injective
  have hδ : δ F (𝟙_ D) (G.obj (𝟙_ C)) = F.map (λ_ _).hom ≫ (λ_ _).inv ≫
      inv (η F) ▷ F.obj (G.obj (𝟙_ C)) := by
    rw [← left_unitality_hom F (G.obj (𝟙_ C))]
    simp
  rw [homEquiv_symm_oplaxUnitProjection, homEquiv_naturality_left_symm, homEquiv_counit,
    counit_naturality, hδ]
  simp only [Category.assoc, Functor.id_obj]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]

/-- At the unit, the unit projection map is an isomorphism, when `η F` is one. -/
lemma isIso_oplaxUnitProjection_tensorUnit [IsIso (η F)] :
    IsIso (adj.oplaxUnitProjection (𝟙_ D)) := by
  rw [oplaxUnitProjection_tensorUnit]
  infer_instance


end UnitProjection

section Pullback

variable {C D C' D' : Type*} [Category* C] [Category* D] [Category* C'] [Category* D']
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory C'] [MonoidalCategory D']
  {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {F' : D' ⥤ C'} {G' : C' ⥤ D'} (adj' : F' ⊣ G')
  [F.OplaxMonoidal] [F'.OplaxMonoidal] {N_D : D ⥤ D'} {N_C : C ⥤ C'} [N_D.OplaxMonoidal]
  [N_C.OplaxMonoidal] (α : N_D ⋙ F' ≅ F ⋙ N_C)

/-- **The unit projection map is compatible with functors commuting with the left adjoints**:
for `α : N_D ⋙ F' ≅ F ⋙ N_C` compatible with the comonoidal structures (`H`), `N_D` carries the
unit projection map `K ⊗ G 𝟙 ⟶ G F K` of `F ⊣ G` to the unit projection map of `F' ⊣ G'` at
`N_D K`, through the comonoidal structure of `N_D`, the mate `β : N_D G ⟶ G' N_C` of `α`, `η N_C`
and `α`. -/
theorem map_oplaxUnitProjection_comp_mateEquiv
    (H : ∀ a b : D, α.hom.app (a ⊗ b) ≫ N_C.map (δ F a b) ≫ δ N_C (F.obj a) (F.obj b) =
      F'.map (δ N_D a b) ≫ δ F' (N_D.obj a) (N_D.obj b) ≫ (α.hom.app a ⊗ₘ α.hom.app b))
    (K : D) :
    N_D.map (adj.oplaxUnitProjection K) ≫ (mateEquiv adj adj' α.hom).app (F.obj K) ≫
        G'.map (α.inv.app K) =
      δ N_D K (G.obj (𝟙_ C)) ≫
        N_D.obj K ◁ ((mateEquiv adj adj' α.hom).app (𝟙_ C) ≫ G'.map (η N_C)) ≫
          adj'.oplaxUnitProjection (N_D.obj K) := by
  apply (adj'.homEquiv _ _).symm.injective
  have h₁ := mateEquiv_counit adj adj' α.hom (F.obj K)
  have h₁' := mateEquiv_counit adj adj' α.hom (𝟙_ C)
  have h₂ := α.hom.naturality (adj.oplaxUnitProjection K)
  have h₃ := adj.map_oplaxUnitProjection_comp_counit K
  have h₄ := adj'.map_oplaxUnitProjection_comp_counit (N_D.obj K)
  have e₁ := right_unitality_hom N_C (F.obj K)
  have e₂ := δ_natural_right N_C (F.obj K) (adj.counit.app (𝟙_ C))
  dsimp at h₁ h₁' h₂ e₂
  simp only [homEquiv_counit, Functor.map_comp, Category.assoc, counit_naturality,
    Functor.comp_obj]
  rw [reassoc_of% h₁, reassoc_of% h₂, ← N_C.map_comp_assoc, h₃, h₄, N_C.map_comp_assoc,
    N_C.map_comp_assoc, ← e₁]
  simp only [Category.assoc]
  rw [← reassoc_of% e₂, reassoc_of% (H K (G.obj (𝟙_ C))), MonoidalCategory.whiskerLeft_comp,
    F'.map_comp]
  simp only [Category.assoc]
  rw [← δ_natural_right_assoc, ← δ_natural_right_assoc]
  have hR : F'.map ((mateEquiv adj adj' α.hom).app (𝟙_ C)) ≫ F'.map (G'.map (η N_C)) ≫
      adj'.counit.app (𝟙_ C') =
      α.hom.app (G.obj (𝟙_ C)) ≫ N_C.map (adj.counit.app (𝟙_ C)) ≫ η N_C := by
    have hn := adj'.counit.naturality (η N_C)
    dsimp at hn
    rw [hn, reassoc_of% h₁']
  have hR' := congrArg (F'.obj (N_D.obj K) ◁ ·) hR
  simp only [MonoidalCategory.whiskerLeft_comp] at hR'
  simp only [tensorHom_def, Category.assoc]
  rw [reassoc_of% hR', ← whisker_exchange_assoc, ← whisker_exchange_assoc,
    ← whisker_exchange_assoc, rightUnitor_naturality_assoc, Iso.hom_inv_id_app]
  simp only [Functor.comp_obj, Category.comp_id]

end Pullback


section Conj

variable {A B : Type*} [Category* A] [Category* B] {L : B ⥤ A} {R : A ⥤ B} (adj : L ⊣ R)
  {S S' : B ⥤ B} {T T' : A ⥤ A}

/-- Mates of squares are compatible with natural transformations of the horizontal functors: if
`θ_B : S ⟶ S'` and `θ_A : T ⟶ T'` intertwine `ξ : S ⋙ L ⟶ L ⋙ T` and `ξ' : S' ⋙ L ⟶ L ⋙ T'`, then
they intertwine the transposes `S (R M) ⟶ R (T M)` and `S' (R M) ⟶ R (T' M)` of
`ξ ≫ T ε` and `ξ' ≫ T' ε`. -/
lemma app_comp_homEquiv_comp_map_counit (ξ : S ⋙ L ⟶ L ⋙ T) (ξ' : S' ⋙ L ⟶ L ⋙ T')
    (θB : S ⟶ S') (θA : T ⟶ T')
    (h : ∀ X, L.map (θB.app X) ≫ ξ'.app X = ξ.app X ≫ θA.app (L.obj X)) (M : A) :
    θB.app (R.obj M) ≫ adj.homEquiv _ _ (ξ'.app (R.obj M) ≫ T'.map (adj.counit.app M)) =
      adj.homEquiv _ _ (ξ.app (R.obj M) ≫ T.map (adj.counit.app M)) ≫ R.map (θA.app M) := by
  rw [← homEquiv_naturality_left, ← homEquiv_naturality_right, reassoc_of% (h (R.obj M)),
    Category.assoc, ← θA.naturality]
  rfl

end Conj


end Adjunction

end CategoryTheory
