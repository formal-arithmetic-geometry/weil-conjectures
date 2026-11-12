/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.KunnethMap
public import WeilConjectures.CategoryTheory.Adjunction.KunnethTranspose
public import WeilConjectures.SixFunctors.NearbyCycles.ExchangeCoherence
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.MonoidalBraided
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperStarCoherence

/-!

# A criterion for the ordinary Künneth map of module objects

Let `Λ` be a commutative condensed ring and
```
P ──p₁──▶ X
│ p₂       │ a_X
▼          ▼
Y ──a_Y──▶ S
```
a commutative square of schemes, with `q = p₂ ≫ a_Y`. The ordinary Künneth map
`κ_{A,B} : L(𝟙)^* Ra_{X*} A ⊗ L(𝟙)^* Ra_{Y*} B ⟶ Rq_* (Lp₁^* A ⊗ Lp₂^* B)` of the two squares
over `S` (`ProEtale.CondensedRing.lowerStarKunnethMap'`) is an isomorphism as soon as

* the base change morphism `La_Y^* Ra_{X*} A ⟶ Rp₂_* Lp₁^* A` of the square is (generic base
  change),
* the projection morphism `Rp₂_* Lp₁^* A ⊗ B ⟶ Rp₂_* (Lp₁^* A ⊗ Lp₂^* B)` of `p₂` is (the
  relative Künneth formula), and
* the projection morphism `Ra_{Y*} B ⊗ Ra_{X*} A ⟶ Ra_{Y*} (B ⊗ La_Y^* Ra_{X*} A)` of `a_Y` is
  (the projection formula over `S`)

(`ProEtale.CondensedRing.isIso_lowerStarKunnethMap'_of_isIso`). This is the abstract
decomposition `CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom` of the Künneth map of the
composite `q = p₂ ≫ a_Y`, on the ambient derived categories of module objects, for an arbitrary
coefficient ring; the version on `Dᵇc(-)⟦ℚ̲̄_ℓ⟧` is
`ProEtale.CondensedRing.isIso_homEquiv_δ_tensorHom_prodUpperStarCounit_of_isIso`.

-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

attribute [local instance] DerivedCategory.braidedCategory'

/-- The transpose of `F f ≫ g` along `F ⊣ G` is invertible if `f` and the transpose of `g` are. -/
lemma _root_.CategoryTheory.Adjunction.isIso_homEquiv_of_eq_map_comp {C D : Type*} [Category C]
    [Category D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {X X' : D} {Y : C} (f : X' ⟶ X)
    (g : F.obj X ⟶ Y) (c : F.obj X' ⟶ Y) (hc : c = F.map f ≫ g) [IsIso f]
    [hg : IsIso (adj.homEquiv _ _ g)] : IsIso (adj.homEquiv _ _ c) := by
  subst hc
  rw [adj.homEquiv_naturality_left]
  infer_instance

/-- The transpose of `F f ≫ ε_B` along `F ⊣ G` is `f`, hence invertible if `f` is. -/
lemma _root_.CategoryTheory.Adjunction.isIso_homEquiv_map_comp_counit {C D : Type*} [Category C]
    [Category D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) {X : D} {B : C} (f : X ⟶ G.obj B)
    [IsIso f] : IsIso (adj.homEquiv _ _ (F.map f ≫ adj.counit.app B)) := by
  rw [adj.homEquiv_naturality_left, adj.homEquiv_unit, adj.right_triangle_components,
    Category.comp_id]
  infer_instance

/-- For `F` compatible with the braidings, the left projection morphism at `(U, A)` is invertible if
the projection morphism at `(A, U')` is, for an isomorphism `U ⟶ U'`. -/
lemma _root_.CategoryTheory.Adjunction.isIso_leftProjectionMorphism_of_isIso {C D : Type*}
    [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D] [BraidedCategory C]
    [BraidedCategory D] {F : D ⥤ C} {G : C ⥤ D} (adj : F ⊣ G) [F.OplaxMonoidal]
    (h : ∀ X Y : D, Functor.OplaxMonoidal.δ F X Y ≫ (β_ (F.obj X) (F.obj Y)).hom =
      F.map (β_ X Y).hom ≫ Functor.OplaxMonoidal.δ F Y X)
    (A : C) {U U' : D} (ι : U ⟶ U') [IsIso ι] [hpm : IsIso (adj.projectionMorphism A U')] :
    IsIso (adj.leftProjectionMorphism U A) := by
  have hn := adj.projectionMorphism_natural_right A ι
  have : IsIso (adj.projectionMorphism A U ≫ G.map (A ◁ F.map ι)) := by
    rw [← hn]
    infer_instance
  have := IsIso.of_isIso_comp_right (adj.projectionMorphism A U) (G.map (A ◁ F.map ι))
  exact adj.isIso_leftProjectionMorphism h U A

open Functor.OplaxMonoidal in
/-- `CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom` with explicit hypotheses. -/
lemma _root_.CategoryTheory.Adjunction.isIso_homEquiv_δ_tensorHom_of_isIso {C₁ C₂ C₃ : Type*}
    [Category C₁] [Category C₂] [Category C₃] [MonoidalCategory C₁] [MonoidalCategory C₂]
    [MonoidalCategory C₃] {R' : C₂ ⥤ C₁} {R : C₁ ⥤ C₂} (adjR : R' ⊣ R) {S' : C₃ ⥤ C₂}
    {S : C₂ ⥤ C₃} (adjS : S' ⊣ S) {Q' : C₃ ⥤ C₁} {Q : C₁ ⥤ C₃} (adjQ : Q' ⊣ Q)
    [R'.OplaxMonoidal] [S'.OplaxMonoidal] [Q'.OplaxMonoidal] (e : Q' ≅ S' ⋙ R')
    (he : ∀ U V : C₃, δ Q' U V ≫ (e.hom.app U ⊗ₘ e.hom.app V) =
      e.hom.app (U ⊗ V) ≫ R'.map (δ S' U V) ≫ δ R' (S'.obj U) (S'.obj V))
    {U V : C₃} {A₁ A₂ : C₁} (c₁ : Q'.obj U ⟶ A₁) (c₂ : Q'.obj V ⟶ A₂) {W : C₂}
    (d₂ : S'.obj V ⟶ W) (i₂ : R'.obj W ⟶ A₂) (hc₂ : e.inv.app V ≫ c₂ = R'.map d₂ ≫ i₂)
    (t₁ : IsIso (adjS.homEquiv _ _ d₂)) (t₂ : IsIso (adjS.leftProjectionMorphism U W))
    (t₃ : IsIso (adjR.homEquiv _ _ (e.inv.app U ≫ c₁)))
    (t₄ : IsIso (adjR.projectionMorphism A₁ W)) (t₅ : IsIso i₂) :
    IsIso (adjQ.homEquiv _ _ (δ Q' U V ≫ (c₁ ⊗ₘ c₂))) :=
  adjR.isIso_homEquiv_δ_tensorHom adjS adjQ e he c₁ c₂ d₂ i₂ hc₂

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ] [IsCommMonObj Λ]

section Transpose

variable {X X₁ Y Y₁ Z Z₁ : Scheme.{u}} {f₁ : Z ⟶ X} {f₂ : Z ⟶ Y} {g : X ⟶ X₁} {h : Y ⟶ Y₁}
  {k : Z ⟶ Z₁} {e₁ : Z₁ ⟶ X₁} {e₂ : Z₁ ⟶ Y₁}

/-- The ordinary Künneth map is the transpose along `Lk^* ⊣ Rk_*` of the oplax structure of
`Lk^*` followed by the tensor product of the counits transported along the pullback comparisons
of the two squares. -/
lemma lowerStarKunnethMap'_eq_homEquiv_counit (sq₁ : CommSq f₁ k g e₁) (sq₂ : CommSq f₂ k h e₂)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y))) :
    lowerStarKunnethMap' Λ sq₁ sq₂ A B =
      (derivedUpperStarLowerStarAdjunction Λ k).homEquiv _ _
        (Functor.OplaxMonoidal.δ L((k)^*⟦Λ⟧) _ _ ≫
          (((pullbackSquareComparison Λ sq₁).hom.app (R((g)_*⟦Λ⟧).obj A) ≫
              L((f₁)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ g).counit.app A)) ⊗ₘ
            ((pullbackSquareComparison Λ sq₂).hom.app (R((h)_*⟦Λ⟧).obj B) ≫
              L((f₂)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ h).counit.app B)))) :=
  Adjunction.tensorHom_comp_eq_homEquiv_δ (derivedUpperStarLowerStarAdjunction Λ k)
    (lowerStarTensorMap' Λ k) (lowerStarTensorMap'_comp_counit Λ k) _ _ _ _
    (Adjunction.exchangeRight_app_comp_counit' _ _ (pullbackSquareComparison Λ sq₁)
      (baseChangeMap Λ sq₁) rfl A)
    (Adjunction.exchangeRight_app_comp_counit' _ _ (pullbackSquareComparison Λ sq₂)
      (baseChangeMap Λ sq₂) rfl B)

/-- The transpose of the transported counit `Lg'^* ... ⟶ Lp'^*` of a square is its base change
morphism. -/
lemma homEquiv_pullbackSquareComparison_comp_counit {X Y X' Y' : Scheme.{u}} {p : X ⟶ Y}
    {g : Y' ⟶ Y} {p' : X' ⟶ Y'} {g' : X' ⟶ X} (sq : CommSq g' p' p g)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X))) :
    (derivedUpperStarLowerStarAdjunction Λ p').homEquiv _ _
        ((pullbackSquareComparison Λ sq).hom.app (R((p)_*⟦Λ⟧).obj A) ≫
          L((g')^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ p).counit.app A)) =
      (baseChangeMap Λ sq).app A := by
  rw [← Adjunction.exchangeRight_app_comp_counit' _ _ (pullbackSquareComparison Λ sq)
    (baseChangeMap Λ sq) rfl A]
  erw [← Adjunction.homEquiv_counit, Equiv.apply_symm_apply]

end Transpose

section Criterion

variable {P X Y S : Scheme.{u}}

/-- `L(f ≫ 𝟙)^* ≅ Lf^*` read through the identity isomorphism `L(𝟙)^* ≅ 𝟭`. -/
lemma leftDerivedUpperStarComp_inv_app_comp_eqToHom_id {W : Scheme.{u}} (f : W ⟶ S)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S))) :
    (leftDerivedUpperStarComp Λ f (𝟙 S)).inv.app K ≫ eqToHom (by rw [Category.comp_id]; rfl) =
      L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ S).hom.app K) := by
  rw [← Iso.app_inv, Iso.inv_comp_eq, Iso.app_hom, leftDerivedUpperStarComp_id_right_app]

-- unifying objects given by composites of derived pullbacks is slow
/-- `leftDerivedUpperStarComp_inv_app_comp_eqToHom_id` followed by an arbitrary `eqToHom`. -/
@[reassoc]
lemma leftDerivedUpperStarComp_inv_app_comp_eqToHom_id' {W : Scheme.{u}} (f : W ⟶ S)
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology S) Ab.{u + 1})
      (condensedRingObj Λ S)))
    {T : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      (condensedRingObj Λ W))} (h : L((f ≫ 𝟙 S)^*⟦Λ⟧).obj K = T) :
    (leftDerivedUpperStarComp Λ f (𝟙 S)).inv.app K ≫ eqToHom h =
      L((f)^*⟦Λ⟧).map ((leftDerivedUpperStarId Λ S).hom.app K) ≫
        eqToHom ((congrArg (fun φ ↦ L((φ)^*⟦Λ⟧).obj K) (Category.comp_id f)).symm.trans h) := by
  rw [← leftDerivedUpperStarComp_inv_app_comp_eqToHom_id Λ f K, Category.assoc, eqToHom_trans]

set_option profiler true in
-- the composition isomorphisms of the derived pullbacks are unfolded
/-- **A criterion for the ordinary Künneth map**: for commutative squares `p₁ ≫ a_X = q ≫ 𝟙`,
`p₂ ≫ a_Y = q ≫ 𝟙` and `p₁ ≫ a_X = p₂ ≫ a_Y`, the Künneth map
`L(𝟙)^* Ra_{X*} A ⊗ L(𝟙)^* Ra_{Y*} B ⟶ Rq_* (Lp₁^* A ⊗ Lp₂^* B)` is an isomorphism if the base
change morphism `La_Y^* Ra_{X*} A ⟶ Rp₂_* Lp₁^* A`, the projection morphism of `p₂` at
`(Lp₁^* A, B)` and the projection morphism of `a_Y` at `(B, Ra_{X*} A)` are isomorphisms. -/
theorem isIso_lowerStarKunnethMap'_of_isIso {p₁ : P ⟶ X} {p₂ : P ⟶ Y} {aX : X ⟶ S}
    {aY : Y ⟶ S} {q : P ⟶ S} (sq₁ : CommSq p₁ q aX (𝟙 S)) (sq₂ : CommSq p₂ q aY (𝟙 S))
    (w : CommSq p₁ p₂ aX aY)
    (A : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ X)))
    (B : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
      (condensedRingObj Λ Y)))
    (h₁ : IsIso ((baseChangeMap Λ w).app A))
    (h₂ : IsIso ((derivedUpperStarLowerStarAdjunction Λ p₂).projectionMorphism
      (L((p₁)^*⟦Λ⟧).obj A) B))
    (h₃ : IsIso ((derivedUpperStarLowerStarAdjunction Λ aY).projectionMorphism B
      (R((aX)_*⟦Λ⟧).obj A))) :
    IsIso (lowerStarKunnethMap' Λ sq₁ sq₂ A B) := by
  obtain rfl : q = p₂ ≫ aY := by simpa using sq₂.w.symm
  rw [lowerStarKunnethMap'_eq_homEquiv_counit]
  -- the transported counit of the first square is the one of `w`, up to `L(𝟙)^* ≅ 𝟭`
  have e₁ : (leftDerivedUpperStarComp Λ p₂ aY).inv.app (L((𝟙 S)^*⟦Λ⟧).obj (R((aX)_*⟦Λ⟧).obj A)) ≫
      (pullbackSquareComparison Λ sq₁).hom.app (R((aX)_*⟦Λ⟧).obj A) ≫
        L((p₁)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ aX).counit.app A) =
      L((p₂)^*⟦Λ⟧).map (L((aY)^*⟦Λ⟧).map
        ((leftDerivedUpperStarId Λ S).hom.app (R((aX)_*⟦Λ⟧).obj A))) ≫
        (pullbackSquareComparison Λ w).hom.app (R((aX)_*⟦Λ⟧).obj A) ≫
          L((p₁)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ aX).counit.app A) := by
    rw [pullbackSquareComparison_hom_app, pullbackSquareComparison_hom_app]
    simp only [Category.assoc]
    rw [leftDerivedUpperStarComp_inv_app_comp_eqToHom_id'_assoc]
    rw [← reassoc_of% ((leftDerivedUpperStarComp Λ p₂ aY).inv.naturality
      ((leftDerivedUpperStarId Λ S).hom.app (R((aX)_*⟦Λ⟧).obj A)))]
  -- the transported counit of the second square is `Lp₂^*` of a transposed identity
  have e₂ : (leftDerivedUpperStarComp Λ p₂ aY).inv.app (L((𝟙 S)^*⟦Λ⟧).obj (R((aY)_*⟦Λ⟧).obj B)) ≫
      (pullbackSquareComparison Λ sq₂).hom.app (R((aY)_*⟦Λ⟧).obj B) ≫
        L((p₂)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ aY).counit.app B) =
      L((p₂)^*⟦Λ⟧).map (L((aY)^*⟦Λ⟧).map
        ((leftDerivedUpperStarId Λ S).hom.app (R((aY)_*⟦Λ⟧).obj B)) ≫
        (derivedUpperStarLowerStarAdjunction Λ aY).counit.app B) ≫ 𝟙 _ := by
    rw [pullbackSquareComparison_hom_app]
    simp only [Category.assoc]
    rw [leftDerivedUpperStarComp_inv_app_comp_eqToHom_id'_assoc]
    rw [← reassoc_of% ((leftDerivedUpperStarComp Λ p₂ aY).inv.naturality
      ((leftDerivedUpperStarId Λ S).hom.app (R((aY)_*⟦Λ⟧).obj B)))]
    simp
  have t₁ : IsIso ((derivedUpperStarLowerStarAdjunction Λ p₂).homEquiv _ _
      ((leftDerivedUpperStarComp Λ p₂ aY).inv.app
          (L((𝟙 S)^*⟦Λ⟧).obj (R((aX)_*⟦Λ⟧).obj A)) ≫
        (pullbackSquareComparison Λ sq₁).hom.app (R((aX)_*⟦Λ⟧).obj A) ≫
          L((p₁)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ aX).counit.app A))) := by
    have hg : IsIso ((derivedUpperStarLowerStarAdjunction Λ p₂).homEquiv _ _
        ((pullbackSquareComparison Λ w).hom.app (R((aX)_*⟦Λ⟧).obj A) ≫
          L((p₁)^*⟦Λ⟧).map ((derivedUpperStarLowerStarAdjunction Λ aX).counit.app A))) := by
      rw [homEquiv_pullbackSquareComparison_comp_counit]
      exact h₁
    exact Adjunction.isIso_homEquiv_of_eq_map_comp _ _ _ _ e₁ (hg := hg)
  have t₂ := Adjunction.isIso_homEquiv_map_comp_counit (derivedUpperStarLowerStarAdjunction Λ aY)
    ((leftDerivedUpperStarId Λ S).hom.app (R((aY)_*⟦Λ⟧).obj B))
  have t₃ := Adjunction.isIso_leftProjectionMorphism_of_isIso
    (derivedUpperStarLowerStarAdjunction Λ aY)
    (fun X Y ↦ (leftDerivedUpperStarTensor_braiding Λ aY X Y).symm) B
    ((leftDerivedUpperStarId Λ S).hom.app (R((aX)_*⟦Λ⟧).obj A)) (hpm := h₃)
  exact Adjunction.isIso_homEquiv_δ_tensorHom_of_isIso (derivedUpperStarLowerStarAdjunction Λ p₂)
    (derivedUpperStarLowerStarAdjunction Λ aY) (derivedUpperStarLowerStarAdjunction Λ (p₂ ≫ aY))
    (leftDerivedUpperStarComp Λ p₂ aY) (fun U V ↦ leftDerivedUpperStarTensor_comp Λ p₂ aY U V)
    _ _ _ (𝟙 _) e₂ t₂ t₃ t₁ h₂ inferInstance

end Criterion

end AlgebraicGeometry.ProEtale.CondensedRing
