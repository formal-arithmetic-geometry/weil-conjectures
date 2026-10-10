/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Adjunction
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.EdgeMap
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Forget
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections

/-!
# The comparison map on étale cohomology in degree zero

For a morphism of schemes `f : X ⟶ Y`, the comparison map
`AlgebraicGeometry.Etale.cohomologyMap f G 0 : H⁰(Y, G) ⟶ H⁰(X, f^* G)` is identified with the
map on global sections `Γ(Y, G) ⟶ Γ(Y, f_* f^* G) = Γ(X, f^* G)` induced by the unit of
`f^* ⊣ f_*`. For a sheaf `F` of `Λ`-modules, the unit of the abelian pullback at the underlying
abelian sheaf of `F` is the underlying map of the unit of the `Λ`-linear pullback, up to an
isomorphism `forget (f^* F) ≅ f^* (forget F)`. Hence the comparison map in degree zero is
bijective as soon as the `Λ`-linear restriction of global sections
`AlgebraicGeometry.Etale.globalSectionsUpperStarMap` is an isomorphism.

## Main statements

- `AlgebraicGeometry.Etale.bijective_cohomologyMap_zero_of_isIso_unit_app`: the comparison in
  degree zero is bijective if the unit is an isomorphism on global sections.
- `AlgebraicGeometry.Etale.exists_unit_app_sheafCompose_forget₂`: the unit of the abelian
  pullback on an underlying abelian sheaf.
- `AlgebraicGeometry.Etale.bijective_cohomologyMap_zero_of_isIso_globalSectionsUpperStarMap`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Abelian

namespace AlgebraicGeometry.Etale

open Scheme

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- In degree zero the edge map `H⁰(Y, f_* G) ⟶ H⁰(X, G)` is bijective for every morphism `f`:
it is the adjunction bijection `(ℤ_Y ⟶ f_* G) ≃ (f^* ℤ_Y ⟶ G)`. -/
lemma bijective_edgeMap_zero (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Function.Bijective fun x : Sheaf.H (((f)_*[AddCommGrpCat.{u + 1}]).obj G) 0 ↦
      Sheaf.H.map ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).counit.app G) 0
        (cohomologyMap f _ 0 x) := by
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  have hb : Function.Bijective (adj.mapExtCounit
      ((constantSheaf _ AddCommGrpCat.{u + 1}).obj (AddCommGrpCat.of (ULift ℤ))) G 0) := by
    have : ⇑(adj.mapExtCounit ((constantSheaf _ AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ))) G 0) = Ext.mk₀ ∘ (adj.homEquiv _ _).symm ∘
          (Ext.homEquiv₀) := by
      funext x
      obtain ⟨a, rfl⟩ := Ext.homEquiv₀.symm.surjective x
      rw [Function.comp_apply, Function.comp_apply, Equiv.apply_symm_apply,
        Ext.homEquiv₀_symm_apply]
      exact adj.mapExtCounit_mk₀ _ _ a
    rw [this]
    exact (Ext.mk₀_bijective _ _).comp ((adj.homEquiv _ _).symm.bijective.comp
      Ext.homEquiv₀.bijective)
  have : (fun x : Sheaf.H (((f)_*[AddCommGrpCat.{u + 1}]).obj G) 0 ↦
      Sheaf.H.map (adj.counit.app G) 0 (cohomologyMap f _ 0 x)) =
        (Ext.precompAddEquiv ((upperStarConstantSheafIso AddCommGrpCat.{u + 1} f).symm.app
          (AddCommGrpCat.of (ULift ℤ))) G 0) ∘ adj.mapExtCounit _ G 0 :=
    funext fun x ↦ map_counit_cohomologyMap f G 0 x
  rw [this]
  exact (AddEquiv.bijective _).comp hb

/-- **The comparison in degree zero.** If the unit `G ⟶ f_* f^* G` of `f^* ⊣ f_*` is an
isomorphism on global sections, the comparison map `H⁰(Y, G) ⟶ H⁰(X, f^* G)` is bijective: it
is the map induced by the unit, followed by the bijective edge map. -/
theorem bijective_cohomologyMap_zero_of_isIso_unit_app
    (G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (h : IsIso (((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app G).hom.app
      (op (⊤_ _)))) :
    Function.Bijective (cohomologyMap f G 0) := by
  let adj := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  have hη : Function.Bijective (Sheaf.H.map (adj.unit.app G) 0) := by
    let e := fun H : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1} ↦
      Sheaf.H.equiv₀ H (terminalIsTerminal (C := Y.Etale))
    have : ⇑(Sheaf.H.map (adj.unit.app G) 0) =
        (e _).symm ∘ (adj.unit.app G).hom.app (op (⊤_ _)) ∘ e G := by
      funext x
      simp only [Function.comp_apply, e]
      exact ((Sheaf.H.equiv₀ _ _).symm_apply_eq.2
        (Sheaf.H.equiv₀_naturality terminalIsTerminal (adj.unit.app G) x)).symm
    rw [this]
    exact (e _).symm.bijective.comp (((ConcreteCategory.isIso_iff_bijective _).1 h).comp
      (e G).bijective)
  have : ⇑(cohomologyMap f G 0) = (fun x ↦ Sheaf.H.map (adj.counit.app ((f)^*[_].obj G)) 0
      (cohomologyMap f _ 0 x)) ∘ Sheaf.H.map (adj.unit.app G) 0 := by
    funext x
    refine Eq.symm ((congrArg (Sheaf.H.map (adj.counit.app _) 0)
      (cohomologyMap_map f 0 (adj.unit.app G) x)).trans ?_)
    refine (Sheaf.H.map_comp_apply _ _ _).symm.trans ?_
    exact (congrArg (fun φ ↦ Sheaf.H.map φ 0 (cohomologyMap f G 0 x))
      (adj.left_triangle_components G)).trans (Sheaf.H.map_id_apply _)
  rw [this]
  exact (bijective_edgeMap_zero f _).comp hη

section Forget

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The abelian unit on an underlying abelian sheaf.** For a sheaf `F` of `Λ`-modules on `Y`,
the unit of the abelian pullback at the underlying abelian sheaf of `F` is the underlying map of
the unit of the `Λ`-linear pullback, followed by an isomorphism `forget (f^* F) ≅ f^* (forget F)`.
The isomorphism is the conjugate, for the composite adjunctions `forget ⋙ f^* ⊣ f_* ⋙ coind`
and `f^* ⋙ forget ⊣ coind ⋙ f_*`, of the identification `f_* ⋙ coind = coind ⋙ f_*`. -/
theorem exists_unit_app_sheafCompose_forget₂
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    ∃ γ : (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj
        ((f)^*[ModuleCat.{u + 1} Λ].obj F) ≅ (f)^*[AddCommGrpCat.{u + 1}].obj
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F),
      (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
          ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) =
        (sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F) ≫
            (f)_*[AddCommGrpCat.{u + 1}].map γ.hom := by
  let fo := forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}
  let adjM := Adjunction.ofIsLeftAdjoint fo
  let R := fo.rightAdjoint
  have : PreservesLimitsOfSize.{u, u + 1} R := adjM.rightAdjoint_preservesLimits
  let bY := Sheaf.sheafComposeAdjunction Y.smallEtaleTopology adjM
  let bX := Sheaf.sheafComposeAdjunction X.smallEtaleTopology adjM
  let aΛ := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  let aA := upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f
  let A₁ := bY.comp aA
  let A₂ := aΛ.comp bX
  let β : (f)_*[AddCommGrpCat.{u + 1}] ⋙ sheafCompose _ R ≅
      sheafCompose _ R ⋙ (f)_*[ModuleCat.{u + 1} Λ] :=
    NatIso.ofComponents (fun _ ↦ Iso.refl _) (by intros; rfl)
  let γ := (conjugateEquiv A₁ A₂).symm β.hom
  have key := unit_conjugateEquiv_symm A₁ A₂ β.hom F
  refine ⟨asIso (γ.app F), ?_⟩
  have hcomm : bY.unit.app ((f)_*[ModuleCat.{u + 1} Λ].obj ((f)^*[ModuleCat.{u + 1} Λ].obj F)) ≫
      (sheafCompose _ R).map ((f)_*[AddCommGrpCat.{u + 1}].map (γ.app F)) =
        (f)_*[ModuleCat.{u + 1} Λ].map (bX.unit.app ((f)^*[ModuleCat.{u + 1} Λ].obj F) ≫
          (sheafCompose _ R).map (γ.app F)) := by
    rfl
  apply (bY.homEquiv _ _).injective
  rw [bY.homEquiv_unit]
  erw [bY.homEquiv_naturality_left, bY.homEquiv_unit]
  simp only [A₁, A₂, Adjunction.comp_unit_app, Functor.comp_map, β] at key
  refine key.trans ?_
  rw [Category.assoc]
  exact congrArg (aΛ.unit.app F ≫ ·) (hcomm.trans (Functor.map_comp _ _ _)).symm

/-- **The comparison in degree zero for sheaves of modules.** Let `F` be a sheaf of `Λ`-modules
on `Y`. If the restriction of global sections `Γ(Y, F) ⟶ Γ(X, f^* F)` is an isomorphism, the
comparison map `H⁰(Y, F) ⟶ H⁰(X, f^* F)` of the underlying abelian sheaf is bijective. -/
theorem bijective_cohomologyMap_zero_of_isIso_globalSectionsUpperStarMap
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (h : IsIso (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) f F)) :
    Function.Bijective (cohomologyMap f
      ((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).obj F) 0) := by
  obtain ⟨γ, hγ⟩ := exists_unit_app_sheafCompose_forget₂ f Λ F
  apply bijective_cohomologyMap_zero_of_isIso_unit_app
  rw [hγ]
  unfold globalSectionsUpperStarMap at h
  have := IsIso.of_isIso_comp_left
    ((Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).hom.app F)
    (((sheafSections Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj (op (⊤_ Y.Etale))).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F) ≫
        ((f)^*[ModuleCat.{u + 1} Λ].obj F).obj.map (PreservesTerminal.iso (Hom.Etale f)).inv.op ≫
          (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
            terminalIsTerminal).inv.app ((f)^*[ModuleCat.{u + 1} Λ].obj F))
  have hη : IsIso (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom.app
      (op (⊤_ _))) := by
    have hc : IsIso (((f)^*[ModuleCat.{u + 1} Λ].obj F).obj.map
        (PreservesTerminal.iso (Hom.Etale f)).inv.op) := Functor.map_isIso _ _
    have hd : IsIso ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
        terminalIsTerminal).inv.app ((f)^*[ModuleCat.{u + 1} Λ].obj F)) := inferInstance
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _ hc hd) this
  have h₂ : IsIso (((f)_*[AddCommGrpCat.{u + 1}].map γ.hom).hom.app (op (⊤_ _))) := by
    have : IsIso ((f)_*[AddCommGrpCat.{u + 1}].map γ.hom) := Functor.map_isIso _ _
    have : IsIso ((sheafToPresheaf _ _).map ((f)_*[AddCommGrpCat.{u + 1}].map γ.hom)) :=
      Functor.map_isIso _ _
    exact (inferInstance : IsIso (((sheafToPresheaf _ _).map
      ((f)_*[AddCommGrpCat.{u + 1}].map γ.hom)).app (op (⊤_ Y.Etale))))
  have h₁ : IsIso (((sheafCompose _ (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1})).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F)).hom.app
        (op (⊤_ _))) :=
    have : IsIso (((sheafToPresheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F)).app
          (op (⊤_ Y.Etale))) := hη
    Functor.map_isIso (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) _
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ h₂

end Forget

end AlgebraicGeometry.Etale
