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

/-- Coinduction from abelian groups to `R`-modules, `A ↦ Hom_ℤ(R, A)`: the equivalence of abelian
groups with `ℤ`-modules followed by coextension of scalars along `ℤ → R`. It is right adjoint to
the forgetful functor, see `ModuleCat.forget₂AddCommGrpAdjunction`. -/
noncomputable def coinduced (R : Type v) [Ring R] : AddCommGrpCat.{v} ⥤ ModuleCat.{v} R :=
  (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.inverse ⋙
    coextendScalars.{0, v, v} (algebraMap ℤ R)

/-- The forgetful functor from `R`-modules to abelian groups is a left adjoint: it is the
restriction of scalars along `ℤ → R` followed by the equivalence of `ℤ`-modules with abelian
groups, and restriction of scalars is left adjoint to coextension of scalars. -/
noncomputable def forget₂AddCommGrpAdjunction (R : Type v) [Ring R] :
    forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v} ⊣ coinduced R :=
  let adj : restrictScalars.{v} (algebraMap ℤ R) ⋙ forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v} ⊣
      (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.inverse ⋙
        coextendScalars.{0, v, v} (algebraMap ℤ R) :=
    (restrictCoextendScalarsAdj (algebraMap ℤ R)).comp
      (forget₂ (ModuleCat.{v} ℤ) AddCommGrpCat.{v}).asEquivalence.toAdjunction
  adj.ofNatIsoLeft (NatIso.ofComponents (fun _ ↦ Iso.refl _))

instance (R : Type v) [Ring R] : (forget₂ (ModuleCat.{v} R) AddCommGrpCat.{v}).IsLeftAdjoint :=
  (forget₂AddCommGrpAdjunction R).isLeftAdjoint

instance (R : Type v) [Ring R] : (coinduced R).IsRightAdjoint :=
  (forget₂AddCommGrpAdjunction R).isRightAdjoint

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

/-- A morphism `x : F a ⟶ b` factors as `F (η a) ≫ F (G x) ≫ ε b` for an adjunction `F ⊣ G`. -/
lemma Adjunction.map_unit_comp_map_map_comp_counit {F : A ⥤ B} {G : B ⥤ A} (adj : F ⊣ G) {a : A}
    {b : B} (x : F.obj a ⟶ b) :
    F.map (adj.unit.app a) ≫ F.map (G.map x) ≫ adj.counit.app b = x := by
  simp

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

/-- The comparison map `f^* (forget₂ G) ⟶ forget₂ (f^* G)` is an isomorphism: for every abelian
sheaf `T` on `X`, precomposition with it is identified with the chain of bijections
`Hom(forget₂ (f^* G), T) ≃ Hom(f^* G, R T) ≃ Hom(G, f_* R T) = Hom(G, R f_* T)
≃ Hom(forget₂ G, f_* T) ≃ Hom(f^* (forget₂ G), T)`, where `R` is the right adjoint of
`forget₂` (coinduction), see `ModuleCat.forget₂AddCommGrpAdjunction`. -/
instance isIso_upperStarForget₂Comparison
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (upperStarForget₂Comparison Λ f G) := by
  rw [isIso_iff_coyoneda_map_bijective]
  intro T
  let adjX := sheafComposeAdjunction X.smallEtaleTopology
    (ModuleCat.forget₂AddCommGrpAdjunction.{u + 1} Λ)
  let adjY := sheafComposeAdjunction Y.smallEtaleTopology
    (ModuleCat.forget₂AddCommGrpAdjunction.{u + 1} Λ)
  let e := (adjX.homEquiv _ T).trans
    (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv G _).trans
      (adjY.homEquiv G ((f)_*[AddCommGrpCat.{u + 1}].obj T)).symm)
  have he (g) : upperStarForget₂Comparison Λ f G ≫ g =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm (e g) := by
    rw [upperStarForget₂Comparison, ← Adjunction.homEquiv_naturality_right_symm]
    congr 1
    apply Sheaf.hom_ext
    ext U : 2
    simp only [e, adjX, adjY, Equiv.trans_apply, Adjunction.homEquiv_unit]
    erw [Adjunction.homEquiv_counit]
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, sheafCompose_map_hom,
      Functor.whiskerRight_app, Functor.map_comp, Category.assoc,
      sheafComposeAdjunction_counit_app_hom, Functor.whiskerLeft_app]
    congr 1
    exact ((ModuleCat.forget₂AddCommGrpAdjunction Λ).map_unit_comp_map_map_comp_counit _).symm
  have : (fun g ↦ upperStarForget₂Comparison Λ f G ≫ g) =
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _).symm ∘ e :=
    funext he
  rw [this]
  exact (Equiv.bijective _).comp e.bijective

/-- The pullback map on global sections of an étale sheaf of `Λ`-modules is an isomorphism if
and only if it is one for the underlying abelian sheaf. -/
theorem isIso_globalSectionsUpperStarMap_iff_forget₂
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) f G) ↔
      IsIso (globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f
        ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj G)) := by
  simp only [globalSectionsUpperStarMap, isIso_comp_left_iff, ← Category.assoc,
    isIso_comp_right_iff]
  rw [← isIso_comp_right_iff _ (((sheafSections _ _).obj (Opposite.op (⊤_ Y.Etale))).map
      ((f)_*[AddCommGrpCat.{u + 1}].map (upperStarForget₂Comparison Λ f G))), ← Functor.map_comp,
    unit_comp_lowerStar_map_upperStarForget₂Comparison]
  exact (isIso_iff_of_reflects_iso (((sheafSections _ _).obj (Opposite.op (⊤_ Y.Etale))).map
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G))
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).symm

end AlgebraicGeometry.Etale
