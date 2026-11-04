/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChangeMate
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory

/-!
# Invertibility of the derived base change morphism

Consider adjunctions `adj : fU ⊣ fL` and `adj' : f'U ⊣ f'L` with exact left adjoints and exact
functors `gU`, `g'U` with `σ : gU ⋙ f'U ≅ fU ⋙ g'U`, as in
`CategoryTheory.Adjunction.derivedBaseChange`. If the underived base change morphism
`fL ⋙ gU ⟶ g'U ⋙ f'L` (the mate of `σ`) is an isomorphism and `g'U` preserves K-injective
complexes, then the derived base change morphism `R(fL) ⋙ D(gU) ⟶ D(g'U) ⋙ R(f'L)` is an
isomorphism (`CategoryTheory.Adjunction.isIso_derivedBaseChange`).

On the image of a K-injective complex `I`, the derived base change morphism is computed by the
underived one (`CategoryTheory.Adjunction.derivedBaseChange_app_fac`): the right derived
functor `R(fL)` is computed by `fL` on `I`, and `R(f'L)` by `f'L` on `g'U(I)`, which is again
K-injective.
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory.Adjunction

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

/-- On the image `Qh P` of an object of the homotopy category, the isomorphism
`D(F) ⋙ D(G) ≅ D(F') ⋙ D(G')` induced by `e : F ⋙ G ≅ F' ⋙ G'` is the image of the morphism
induced by `e` on homotopy categories, up to the factorization isomorphisms. -/
lemma mapDerivedCategorySquareIso_hom_app_Qh_obj_factorsh
    {C D E Z : Type*} [Category* C] [Category* D] [Category* E] [Category* Z]
    [Abelian C] [Abelian D] [Abelian E] [Abelian Z]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [HasDerivedCategory E] [HasDerivedCategory Z]
    (F : C ⥤ D) (G : D ⥤ Z) (F' : C ⥤ E) (G' : E ⥤ Z)
    [F.Additive] [G.Additive] [F'.Additive] [G'.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (e : F ⋙ G ≅ F' ⋙ G') (P : HomotopyCategory C (.up ℤ)) :
    (Functor.mapDerivedCategorySquareIso e).hom.app (DerivedCategory.Qh.obj P) ≫
        G'.mapDerivedCategory.map (F'.mapDerivedCategoryFactorsh.hom.app P) ≫
        G'.mapDerivedCategoryFactorsh.hom.app ((F'.mapHomotopyCategory (.up ℤ)).obj P) =
      G.mapDerivedCategory.map (F.mapDerivedCategoryFactorsh.hom.app P) ≫
        G.mapDerivedCategoryFactorsh.hom.app ((F.mapHomotopyCategory (.up ℤ)).obj P) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory e.hom (.up ℤ)).app P) := by
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app, Category.assoc]
  have hc := Functor.mapDerivedCategoryCompIso_fach F' G' P
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  erw [hc, Functor.mapDerivedCategoryNatIso_fach]
  have hc := Functor.mapDerivedCategoryCompIso_fach F G P
  simp only [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at hc
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at hc
  erw [← hc]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]

section

variable {C₁ C₂ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
  {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]

/-- The morphism induced on homotopy categories by the mate of a square is the mate, computed
with the adjunction induced on homotopy categories, of the morphism induced by the square. -/
lemma mapHomotopyCategory_mateEquiv_app (adj : L ⊣ R) (adj' : L' ⊣ R')
    (σ : TwoSquare G L L' G') (K : HomotopyCategory C₁ (.up ℤ)) :
    (NatTrans.mapHomotopyCategory (mateEquiv adj adj' σ).natTrans (.up ℤ)).app K =
      (adj'.mapHomotopyCategory (.up ℤ)).unit.app
          ((G.mapHomotopyCategory (.up ℤ)).obj ((R.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        (R'.mapHomotopyCategory (.up ℤ)).map
          ((NatTrans.mapHomotopyCategory σ.natTrans (.up ℤ)).app
            ((R.mapHomotopyCategory (.up ℤ)).obj K)) ≫
        (R'.mapHomotopyCategory (.up ℤ)).map
          ((G'.mapHomotopyCategory (.up ℤ)).map
            ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient C₄ (.up ℤ)).map _ =
    (HomotopyCategory.quotient C₄ (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient C₄ (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient C₄ (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [mateEquiv_apply, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Functor.comp_map]
  exact congrArg (fun t ↦ _ ≫ _ ≫ t) (Category.comp_id _)

end

section

variable {C₁ C₂ C₃ C₄ : Type*}
  [Category* C₁] [Category* C₂] [Category* C₃] [Category* C₄]
  [Abelian C₁] [Abelian C₂] [Abelian C₃] [Abelian C₄]
  [HasDerivedCategory C₁] [HasDerivedCategory C₂]
  [HasDerivedCategory C₃] [HasDerivedCategory C₄]
  [Abelian.HasKInjectiveResolutions C₁] [Abelian.HasKInjectiveResolutions C₃]
  {L : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} {L' : C₄ ⥤ C₃} {R' : C₃ ⥤ C₄}
  {G : C₂ ⥤ C₄} {G' : C₁ ⥤ C₃}
  [L.Additive] [R.Additive] [L'.Additive] [R'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits L] [PreservesFiniteColimits L]
  [PreservesFiniteLimits L'] [PreservesFiniteColimits L']
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits G'] [PreservesFiniteColimits G']

/-- On the image of an object `K` of the homotopy category, precomposed with the unit of `R(R)`,
the mate of a square `θ : D(G) ⋙ D(L') ⟶ D(L) ⋙ D(G')` under the derived adjunctions
`D(L) ⊣ R(R)` and `D(L') ⊣ R(R')` is the image of the underived mate `R ⋙ G ⟶ G' ⋙ R'` of
`σ`, followed by the unit of `R(R')`, provided `θ` is induced by `σ` on homotopy
categories (`hθ`). -/
lemma mapDerivedCategoryRightDerivedAdjunction_mateEquiv_app_fac (adj : L ⊣ R)
    (adj' : L' ⊣ R') (σ : TwoSquare G L L' G')
    (θ : TwoSquare G.mapDerivedCategory L.mapDerivedCategory L'.mapDerivedCategory
      G'.mapDerivedCategory)
    (hθ : ∀ N : HomotopyCategory C₂ (.up ℤ),
      θ.natTrans.app (DerivedCategory.Qh.obj N) ≫
          G'.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N) ≫
          G'.mapDerivedCategoryFactorsh.hom.app ((L.mapHomotopyCategory (.up ℤ)).obj N) =
        L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N) ≫
          L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
          DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ.natTrans (.up ℤ)).app N))
    (K : HomotopyCategory C₁ (.up ℤ)) :
    G.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
        (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
          adj'.mapDerivedCategoryRightDerivedAdjunction θ).natTrans.app
          (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory (mateEquiv adj adj' σ).natTrans (.up ℤ)).app K) ≫
        R'.rightDerivedFunctorUnit.app ((G'.mapHomotopyCategory (.up ℤ)).obj K) ≫
        R'.rightDerivedFunctor.map (G'.mapDerivedCategoryFactorsh.inv.app K) := by
  have hmate (Z : DerivedCategory C₁) :
      (mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
          adj'.mapDerivedCategoryRightDerivedAdjunction θ).natTrans.app Z =
        adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app
            (G.mapDerivedCategory.obj (R.rightDerivedFunctor.obj Z)) ≫
          R'.rightDerivedFunctor.map (θ.natTrans.app (R.rightDerivedFunctor.obj Z)) ≫
          R'.rightDerivedFunctor.map (G'.mapDerivedCategory.map
            (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app Z)) := by
    simp [mateEquiv_apply]
  set N := (R.mapHomotopyCategory (.up ℤ)).obj K
  set u := R.rightDerivedFunctorUnit.app K
  have h₁ := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (G.mapDerivedCategory.map u)
  have h₂ := θ.natTrans.naturality u
  have h₃ := (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso C₁ (.up ℤ)) L.mapDerivedCategoryFactorsh.hom
    R.rightDerivedFunctorUnit K
  change L.mapDerivedCategory.map u ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Qh.obj K) =
    _ at h₃
  have h₄ := mapHomotopyCategory_mateEquiv_app adj adj' σ K
  have h₅ := R'.rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory σ.natTrans (.up ℤ)).app N ≫
      (G'.mapHomotopyCategory (.up ℤ)).map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K))
  have h₆ := (adj'.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
    (HomotopyCategory.quasiIso C₄ (.up ℤ)) L'.mapDerivedCategoryFactorsh.hom
    R'.rightDerivedFunctorUnit ((G.mapHomotopyCategory (.up ℤ)).obj N)
  change adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app
      (DerivedCategory.Qh.obj ((G.mapHomotopyCategory (.up ℤ)).obj N)) ≫ _ = _ at h₆
  have h₇ := adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality
    (G.mapDerivedCategoryFactorsh.hom.app N)
  have h₈ := hθ N
  have h₉ := G'.mapDerivedCategoryFactorsh.hom.naturality
    ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)
  simp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
    at h₁ h₂ h₅ h₇ h₉
  rw [hmate, reassoc_of% h₁]
  simp only [← Functor.map_comp]
  rw [reassoc_of% h₂, ← Functor.map_comp (G'.mapDerivedCategory), h₃]
  erw [h₄]
  erw [← Functor.map_comp (R'.mapHomotopyCategory (.up ℤ))]
  erw [Functor.map_comp DerivedCategory.Qh, Category.assoc, reassoc_of% h₅]
  erw [← reassoc_of% h₆, reassoc_of% h₇]
  congr 1
  have key : θ.natTrans.app (DerivedCategory.Qh.obj N) ≫
      G'.mapDerivedCategory.map (L.mapDerivedCategoryFactorsh.hom.app N ≫
        DerivedCategory.Qh.map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) =
      L'.mapDerivedCategory.map (G.mapDerivedCategoryFactorsh.hom.app N) ≫
        L'.mapDerivedCategoryFactorsh.hom.app ((G.mapHomotopyCategory (.up ℤ)).obj N) ≫
        DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ.natTrans (.up ℤ)).app N) ≫
        DerivedCategory.Qh.map
          ((G'.mapHomotopyCategory (.up ℤ)).map ((adj.mapHomotopyCategory (.up ℤ)).counit.app K)) ≫
        G'.mapDerivedCategoryFactorsh.inv.app K := by
    rw [← cancel_mono (G'.mapDerivedCategoryFactorsh.hom.app K)]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.map_comp]
    rw [h₉, reassoc_of% h₈]
    erw [Category.comp_id]
  rw [key]
  simp only [Functor.map_comp]
  simp only [Category.assoc]

/-- **The derived base change morphism on the homotopy category.** Precomposed with the unit of
`R(R)`, the derived base change morphism `R(R) ⋙ D(G) ⟶ D(G') ⋙ R(R')` (the mate of the
isomorphism `D(G) ⋙ D(L') ≅ D(L) ⋙ D(G')` induced by `e : G ⋙ L' ≅ L ⋙ G'`) is the image of
the underived base change morphism `R ⋙ G ⟶ G' ⋙ R'` (the mate of `e`), followed by the unit
of `R(R')`. -/
lemma derivedBaseChange_app_fac (adj : L ⊣ R) (adj' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ G')
    (K : HomotopyCategory C₁ (.up ℤ)) :
    G.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app K) ≫
        (adj.derivedBaseChange adj' e).natTrans.app (DerivedCategory.Qh.obj K) =
      G.mapDerivedCategoryFactorsh.hom.app ((R.mapHomotopyCategory (.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map
          ((NatTrans.mapHomotopyCategory
            (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)).natTrans (.up ℤ)).app K) ≫
        R'.rightDerivedFunctorUnit.app ((G'.mapHomotopyCategory (.up ℤ)).obj K) ≫
        R'.rightDerivedFunctor.map (G'.mapDerivedCategoryFactorsh.inv.app K) :=
  mapDerivedCategoryRightDerivedAdjunction_mateEquiv_app_fac adj adj' _ _
    (mapDerivedCategorySquareIso_hom_app_Qh_obj_factorsh G L' L G' e) K

/-- **Invertibility of the derived base change morphism.** If the underived base change
morphism `R ⋙ G ⟶ G' ⋙ R'` (the mate of `e : G ⋙ L' ≅ L ⋙ G'`) is an isomorphism and `G'`
preserves K-injective complexes, then the derived base change morphism
`R(R) ⋙ D(G) ⟶ D(G') ⋙ R(R')` is an isomorphism. -/
theorem isIso_derivedBaseChange_app (adj : L ⊣ R) (adj' : L' ⊣ R') (e : G ⋙ L' ≅ L ⋙ G')
    [G'.PreservesKInjectiveComplexes]
    [IsIso (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)).natTrans]
    (M : DerivedCategory C₁) :
    IsIso ((adj.derivedBaseChange adj' e).natTrans.app M) := by
  let β := mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)
  let eh : (R ⋙ G).mapHomotopyCategory (.up ℤ) ≅ (G' ⋙ R').mapHomotopyCategory (.up ℤ) :=
    { hom := NatTrans.mapHomotopyCategory β.natTrans _
      inv := NatTrans.mapHomotopyCategory (inv β.natTrans) _
      hom_inv_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, IsIso.hom_inv_id,
          NatTrans.mapHomotopyCategory_id]
      inv_hom_id := by
        rw [← NatTrans.mapHomotopyCategory_comp, IsIso.inv_hom_id,
          NatTrans.mapHomotopyCategory_id] }
  have : IsIso (NatTrans.mapHomotopyCategory
      (mateEquiv adj adj' (TwoSquare.mk _ _ _ _ e.hom)).natTrans (.up ℤ)) := eh.isIso_hom
  obtain ⟨K₀, ⟨eK⟩⟩ : ∃ K₀ : CochainComplex C₁ ℤ, Nonempty (DerivedCategory.Q.obj K₀ ≅ M) :=
    ⟨_, ⟨DerivedCategory.Q.objObjPreimageIso M⟩⟩
  obtain ⟨I, _, i, _, _⟩ := HasKInjectiveResolutions.exists_isKInjective K₀
  rw [NatTrans.isIso_app_iff_of_iso _ (eK.symm ≪≫ asIso (DerivedCategory.Q.map i) :
    M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))]
  have : IsIso (R'.rightDerivedFunctorUnit.app ((G'.mapHomotopyCategory (.up ℤ)).obj
      ((HomotopyCategory.quotient _ _).obj I))) :=
    inferInstanceAs (IsIso (R'.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj
      ((G'.mapHomologicalComplex (.up ℤ)).obj I))))
  have : IsIso (G.mapDerivedCategory.map
      (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I)) ≫
        (adj.derivedBaseChange adj' e).natTrans.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) := by
    rw [derivedBaseChange_app_fac]
    infer_instance
  exact IsIso.of_isIso_comp_left (G.mapDerivedCategory.map
    (R.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj I))) _

end

end CategoryTheory.Adjunction
