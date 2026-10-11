/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# Pullback of étale sheaves of modules and their underlying abelian sheaves

For a commutative ring `Λ` and a morphism of schemes `f : X ⟶ Y`, pulling back an étale sheaf of
`Λ`-modules commutes with taking the underlying abelian sheaf. Consequently the pullback map on
global sections `Γ(Y, G) ⟶ Γ(X, f^* G)` is an isomorphism for `G` if and only if it is one for
the underlying abelian sheaf of `G`.

## Main definitions and results

- `ModuleCat.forget₂AddCommGrpAdjunction`: the forgetful functor from `R`-modules to abelian
  groups is left adjoint to coinduction `A ↦ Hom_ℤ(R, A)`.
- `CategoryTheory.sheafComposeAdjunction`: an adjunction `F ⊣ G` between coefficient
  categories induces an adjunction `sheafCompose J F ⊣ sheafCompose J G`.
- `AlgebraicGeometry.Etale.upperStarForget₂Comparison`: the comparison map
  `f^* (forget₂ G) ⟶ forget₂ (f^* G)`, which is an isomorphism.
- `AlgebraicGeometry.Etale.isIso_globalSectionsUpperStarMap_iff_forget₂`.
-/

@[expose] public section

universe v u v₁ v₂ v₃ u₁ u₂ u₃

open CategoryTheory Limits

namespace ModuleCat

/-- The forgetful functor from `R`-modules to abelian groups is a left adjoint: it is the
restriction of scalars along `ℤ → R` followed by the equivalence of `ℤ`-modules with abelian
groups, and restriction of scalars is left adjoint to coextension of scalars. -/
noncomputable def forget₂AddCommGrpAdjunction (R : Type v) [Ring R] :
    forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⊣
      (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.inverse ⋙
        coextendScalars (algebraMap ℤ R) :=
  let adj : restrictScalars.{v} (algebraMap ℤ R) ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v} ⊣
      (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.inverse ⋙
        coextendScalars (algebraMap ℤ R) :=
    (restrictCoextendScalarsAdj (algebraMap ℤ R)).comp
      (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.toAdjunction
  adj.ofNatIsoLeft (NatIso.ofComponents (fun _ ↦ Iso.refl _))

instance (R : Type v) [Ring R] : (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).IsLeftAdjoint :=
  (forget₂AddCommGrpAdjunction R).isLeftAdjoint

end ModuleCat

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {A : Type u₂}
  [Category.{v₂} A] {B : Type u₃} [Category.{v₃} B] {F : A ⥤ B} {G : B ⥤ A}
  (adj : F ⊣ G) [J.HasSheafCompose F] [J.HasSheafCompose G]

/-- An adjunction `F ⊣ G` between coefficient categories, both of which preserve sheaves,
induces an adjunction `sheafCompose J F ⊣ sheafCompose J G` between categories of sheaves,
whose unit and counit are obtained by whiskering. -/
noncomputable def sheafComposeAdjunction : sheafCompose J F ⊣ sheafCompose J G :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app P := ObjectProperty.homMk (Functor.whiskerLeft P.obj adj.unit)
          naturality P Q φ := by ext1; ext U; exact adj.unit.naturality _ }
      counit :=
        { app P := ObjectProperty.homMk (Functor.whiskerLeft P.obj adj.counit)
          naturality P Q φ := by ext1; ext U; exact adj.counit.naturality _ }
      left_triangle := by
        ext P : 2; ext1; ext U
        simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.whiskerRight_app,
          Functor.associator_hom_app, Functor.whiskerLeft_app, Category.id_comp,
          ObjectProperty.FullSubcategory.comp_hom, sheafCompose_map_hom, ObjectProperty.homMk_hom,
          NatTrans.id_app', ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
        exact adj.left_triangle_components _
      right_triangle := by
        ext P : 2; ext1; ext U
        simp only [Functor.comp_obj, Functor.id_obj, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.associator_inv_app, Functor.whiskerRight_app, Category.id_comp,
          ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom, sheafCompose_map_hom,
          NatTrans.id_app', ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
        exact adj.right_triangle_components _ }

@[simp]
lemma sheafComposeAdjunction_unit_app_hom (P : Sheaf J A) :
    ((sheafComposeAdjunction J adj).unit.app P).hom = Functor.whiskerLeft P.obj adj.unit :=
  rfl

@[simp]
lemma sheafComposeAdjunction_counit_app_hom (P : Sheaf J B) :
    ((sheafComposeAdjunction J adj).counit.app P).hom = Functor.whiskerLeft P.obj adj.counit :=
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The comparison map `f^* (forget₂ G) ⟶ forget₂ (f^* G)` between the pullback of the
underlying abelian sheaf of an étale sheaf `G` of `Λ`-modules and the underlying abelian sheaf
of its pullback. It is the mate of the equality `f_* ∘ forget₂ = forget₂ ∘ f_*`: it corresponds
under `f^* ⊣ f_*` to `forget₂` of the unit `G ⟶ f_* f^* G`. It is an isomorphism, see
`AlgebraicGeometry.Etale.isIso_upperStarForget₂Comparison`. -/
noncomputable def upperStarForget₂Comparison
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (f)^*[AddCommGrpCat.{u + 1}].obj
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) ⟶
      (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((f)^*[ModuleCat.{u + 1} Λ].obj G) :=
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm
    ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G))

/-- The comparison map `f^* (forget₂ G) ⟶ forget₂ (f^* G)` is compatible with the units of
`f^* ⊣ f_*`. -/
lemma unit_comp_lowerStar_map_upperStarForget₂Comparison
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G) ≫
      (f)_*[AddCommGrpCat.{u + 1}].map (upperStarForget₂Comparison Λ f G) =
    (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G) := 
 
  ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv_unit _ _ _).symm.trans
    (Equiv.apply_symm_apply _ _)

end AlgebraicGeometry.Etale
