/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.BaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSectionsRestrictionBasic
public import WeilConjectures.SixFunctors.Etale.Derived.UnitLerayQuotient

/-!
# Restriction of derived global sections and the underlying abelian sheaves

Let `Λ` be a ring. For a scheme `X`, forgetting the `Λ`-module structure of étale sheaves of
`Λ`-modules gives an exact functor `S_X : Sh(X_ét, Λ) ⥤ Sh(X_ét, ℤ)`, compatible with global
sections. We construct the base change morphism
`RΓ(X, -) ⋙ D(forget) ⟶ D(S_X) ⋙ RΓ(X, -)`
(`AlgebraicGeometry.Etale.rightDerivedGlobalSectionsForget`) and show that it is compatible
with the restriction maps `RΓ(X, K) ⟶ RΓ(Y, f^* K)`
(`AlgebraicGeometry.Etale.globalSectionsRestriction_forget`).

## Main definitions

- `AlgebraicGeometry.Etale.globalSectionsForgetIso`: `Γ(X, -) ⋙ forget ≅ S_X ⋙ Γ(X, -)`.
- `AlgebraicGeometry.Etale.rightDerivedGlobalSectionsForget`: the induced base change morphism
  on derived global sections.
- `AlgebraicGeometry.Etale.mapDerivedUpperStarForgetIso`: the isomorphism
  `D(S_Y) ⋙ D(f^*) ≅ D(f^*) ⋙ D(S_X)` induced by the comparison of pullbacks.

## Main results

- `AlgebraicGeometry.Etale.forget_map_globalSectionsUpperStarMap`: the pullback of global
  sections commutes with forgetting the module structure.
- `AlgebraicGeometry.Etale.globalSectionsRestriction_forget`: the restriction maps of derived
  global sections commute with forgetting the module structure.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- The restriction map of derived global sections, precomposed with the unit
`Γ(Y, K) ⟶ RΓ(Y, K)`, is computed by the pullback of global sections `Γ(Y, K) ⟶ Γ(X, f^* K)` on
the complex `K`. -/
lemma rightDerivedFunctorUnit_app_comp_globalSectionsRestriction (A : Type*)
    [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : CochainComplex (Sheaf Y.smallEtaleTopology A) ℤ) :
    (Sheaf.Γ Y.smallEtaleTopology A).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj K) ≫
        globalSectionsRestriction f
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex (globalSectionsUpperStarNatTrans A f) (.up ℤ)).app K)) ≫
        (Sheaf.Γ X.smallEtaleTopology A).rightDerivedFunctorUnit.app
          ((HomotopyCategory.quotient _ _).obj (((f)^*[A]).mapHomologicalComplex _ |>.obj K)) ≫
        (rightDerivedGlobalSections A X).map
          (((f)^*[A]).mapDerivedCategoryFactorsh.inv.app
            ((HomotopyCategory.quotient _ _).obj K)) := by
  have h := rightDerivedGlobalSections_map_unit_quotient A f K
  erw [reassoc_of% (DerivedCategory.quotientCompQhIso_inv_naturality
    ((NatTrans.mapHomologicalComplex (globalSectionsUpperStarNatTrans A f) (.up ℤ)).app K)),
    Iso.hom_inv_id_app_assoc] at h
  rw [← reassoc_of% h, globalSectionsRestriction, ← Functor.map_comp, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- The forgetful functor from `Λ`-modules to abelian groups preserves finite limits. -/
instance preservesFiniteLimits_forget₂_moduleCat :
    PreservesFiniteLimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) where
  preservesFiniteLimits _ := ⟨fun {_} ↦ inferInstance⟩

/-- The forgetful functor from `Λ`-modules to abelian groups preserves finite colimits. -/
instance preservesFiniteColimits_forget₂_moduleCat :
    PreservesFiniteColimits (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}) where
  preservesFiniteColimits _ := ⟨fun {_} ↦ inferInstance⟩

/-- Global sections commute with forgetting the module structure:
`Γ(X, -) ⋙ forget ≅ S_X ⋙ Γ(X, -)`. -/
noncomputable def globalSectionsForgetIso (X : Scheme.{u}) :
    Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⋙
        forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1} ≅
      moduleAbelianForget Λ X ⋙ Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  Functor.isoWhiskerRight
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology _ terminalIsTerminal) _ ≪≫
    Functor.isoWhiskerLeft (moduleAbelianForget Λ X)
      (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology _ terminalIsTerminal).symm

/-- The components of `AlgebraicGeometry.Etale.globalSectionsForgetIso`. -/
lemma globalSectionsForgetIso_hom_app (X : Scheme.{u})
    (G : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (globalSectionsForgetIso Λ X).hom.app G =
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
          ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology _ terminalIsTerminal).hom.app G) ≫
        (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology _ terminalIsTerminal).inv.app
          ((moduleAbelianForget Λ X).obj G) :=
  rfl

/-- The comparison `f^* (S_Y G) ⟶ S_X (f^* G)` of pullbacks is adjoint to the image under `S_Y` of
the unit `G ⟶ f_* f^* G`. -/
@[reassoc]
lemma unit_app_moduleAbelianForget_comp_lowerStar_map {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((moduleAbelianForget Λ Y).obj G) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map ((moduleAbelianUpperStarComparison Λ f).app G) =
    (moduleAbelianForget Λ Y).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G) := by
  have h := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
    ((moduleAbelianForget Λ Y).obj G)
    ((moduleAbelianForget Λ X).obj ((f)^*[ModuleCat.{u + 1} Λ].obj G))).apply_symm_apply
    ((moduleAbelianForget Λ Y).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G))
  rwa [Adjunction.homEquiv_unit] at h

/-- The pullback of global sections commutes with forgetting the module structure. -/
lemma forget_map_globalSectionsUpperStarMap {X Y : Scheme.{u}} (f : X ⟶ Y)
    (G : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map
        (globalSectionsUpperStarMap (ModuleCat.{u + 1} Λ) f G) ≫
      (globalSectionsForgetIso Λ X).hom.app ((f)^*[ModuleCat.{u + 1} Λ].obj G) =
    (globalSectionsForgetIso Λ Y).hom.app G ≫
      globalSectionsUpperStarMap AddCommGrpCat.{u + 1} f ((moduleAbelianForget Λ Y).obj G) ≫
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        ((moduleAbelianUpperStarComparison Λ f).app G) := by
  have hu := unit_app_moduleAbelianForget_comp_lowerStar_map Λ f G
  have hn := (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
    terminalIsTerminal).inv.naturality ((moduleAbelianUpperStarComparison Λ f).app G)
  have hs := ((moduleAbelianUpperStarComparison Λ f).app G).hom.naturality
    (PreservesTerminal.iso f.Etale).inv.op
  simp only [globalSectionsForgetIso_hom_app, globalSectionsUpperStarMap, Functor.map_comp,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  have hu' := congrArg
    ((sheafSections Y.smallEtaleTopology AddCommGrpCat.{u + 1}).obj (op (⊤_ Y.Etale))).map hu
  rw [Functor.map_comp] at hu'
  rw [← Functor.map_comp_assoc (forget₂ _ _)
    ((Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
      terminalIsTerminal).inv.app _), Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.id_comp]
  erw [← hn, reassoc_of% hs, reassoc_of% hu']
  rfl

/-- The base change morphism `RΓ(X, -) ⋙ D(forget) ⟶ D(S_X) ⋙ RΓ(X, -)` comparing derived global
sections of étale sheaves of `Λ`-modules with those of the underlying abelian sheaves. -/
noncomputable def rightDerivedGlobalSectionsForget (X : Scheme.{u}) :
    rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X ⋙
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory ⟶
      (moduleAbelianForget Λ X).mapDerivedCategory ⋙
        rightDerivedGlobalSections AddCommGrpCat.{u + 1} X :=
  Functor.rightDerivedFunctorBaseChange (globalSectionsForgetIso Λ X).hom

/-- The base change morphism `rightDerivedGlobalSectionsForget` precomposed with the unit
`Γ(X, K) ⟶ RΓ(X, K)` is `Γ(X, K) ≅ Γ(X, S_X K)` followed by the unit of the abelian derived global
sections. -/
lemma rightDerivedGlobalSectionsForget_app_fac (X : Scheme.{u})
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategoryFactorsh.inv.app
          (((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomotopyCategory (.up ℤ)).obj
            K) ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory.map
          ((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnit.app K) ≫
        (rightDerivedGlobalSectionsForget Λ X).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory (globalSectionsForgetIso Λ X).hom
          (.up ℤ)).app K) ≫
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorUnit.app
          (((moduleAbelianForget Λ X).mapHomotopyCategory (.up ℤ)).obj K) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((moduleAbelianForget Λ X).mapDerivedCategoryFactorsh.inv.app K) :=
  Functor.rightDerivedFunctorBaseChange_app_fac _ K

/-- The isomorphism `D(S_Y) ⋙ D(f^*) ≅ D(f^*) ⋙ D(S_X)` induced by the comparison of the pullbacks
of étale sheaves of `Λ`-modules and of abelian étale sheaves along `f : X ⟶ Y`. -/
noncomputable def mapDerivedUpperStarForgetIso {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (moduleAbelianForget Λ Y).mapDerivedCategory ⋙
        ((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategory ≅
      ((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory ⋙
        (moduleAbelianForget Λ X).mapDerivedCategory :=
  Functor.mapDerivedCategorySquareIso (moduleAbelianUpperStarIso Λ f)

/-- The pullback of global sections commutes with forgetting the module structure, on complexes
of étale sheaves of `Λ`-modules. -/
lemma forget_mapHomologicalComplex_globalSectionsUpperStarNatTrans {X Y : Scheme.{u}}
    (f : X ⟶ Y) (K : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex
          (globalSectionsUpperStarNatTrans (ModuleCat.{u + 1} Λ) f) (.up ℤ)).app K) ≫
      (NatTrans.mapHomologicalComplex (globalSectionsForgetIso Λ X).hom (.up ℤ)).app
        (((f)^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex _ |>.obj K) ≫
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (moduleAbelianUpperStarIso Λ f).inv (.up ℤ)).app K) =
    (NatTrans.mapHomologicalComplex (globalSectionsForgetIso Λ Y).hom (.up ℤ)).app K ≫
      (NatTrans.mapHomologicalComplex
        (globalSectionsUpperStarNatTrans AddCommGrpCat.{u + 1} f) (.up ℤ)).app
          ((moduleAbelianForget Λ Y).mapHomologicalComplex _ |>.obj K) := by
  ext n : 1
  have h := forget_map_globalSectionsUpperStarMap Λ f (K.X n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, globalSectionsUpperStarNatTrans_app]
  erw [reassoc_of% h, ← Functor.map_comp, (moduleAbelianUpperStarIso Λ f).hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

-- The square of `globalSectionsRestriction_forget` at a complex, after precomposition with the
-- unit `Γ(Y, K) ⟶ RΓ(Y, K)`.
private lemma globalSectionsRestriction_forget_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategoryFactorsh.inv.app
          (((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj K)) ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory.map
          ((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ _).obj K)) ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory.map
          (globalSectionsRestriction f
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) ≫
        (rightDerivedGlobalSectionsForget Λ X).app
          (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          ((mapDerivedUpperStarForgetIso Λ f).inv.app
            (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) =
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategoryFactorsh.inv.app
          (((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj K)) ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory.map
          ((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnit.app
            ((HomotopyCategory.quotient _ _).obj K)) ≫
        (rightDerivedGlobalSectionsForget Λ Y).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) ≫
        globalSectionsRestriction f ((moduleAbelianForget Λ Y).mapDerivedCategory.obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) := by
  have h1 := rightDerivedFunctorUnit_app_comp_globalSectionsRestriction (ModuleCat.{u + 1} Λ) f K
  have h1' := rightDerivedFunctorUnit_app_comp_globalSectionsRestriction AddCommGrpCat.{u + 1} f
    ((moduleAbelianForget Λ Y).mapHomologicalComplex (.up ℤ) |>.obj K)
  have h2 := rightDerivedGlobalSectionsForget_app_fac Λ Y ((HomotopyCategory.quotient _ _).obj K)
  have h2' := rightDerivedGlobalSectionsForget_app_fac Λ X ((HomotopyCategory.quotient _ _).obj
      (((f)^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ) |>.obj K))
  have h3 := Functor.mapDerivedCategorySquareIso_inv_app_Qh_obj (moduleAbelianUpperStarIso Λ f)
    ((HomotopyCategory.quotient _ _).obj K)
  have h4 : (rightDerivedGlobalSections AddCommGrpCat.{u + 1} Y).map
        ((moduleAbelianForget Λ Y).mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.quotient _ _).obj K)) ≫
      globalSectionsRestriction f ((moduleAbelianForget Λ Y).mapDerivedCategory.obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) =
      globalSectionsRestriction f (DerivedCategory.Qh.obj
          (((moduleAbelianForget Λ Y).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj K))) ≫
        (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
          (((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategory.map
            ((moduleAbelianForget Λ Y).mapDerivedCategoryFactorsh.inv.app
              ((HomotopyCategory.quotient _ _).obj K))) :=
    globalSectionsRestriction_naturality f _
  have h5 := (rightDerivedGlobalSectionsForget Λ X).naturality
    (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.quotient _ _).obj K))
  have h6 : (forget₂ (ModuleCat.{u + 1} Λ)
        AddCommGrpCat.{u + 1}).mapDerivedCategoryFactorsh.inv.app
          (((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj K)) ≫
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory.map
        (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex
            (globalSectionsUpperStarNatTrans (ModuleCat.{u + 1} Λ) f) (.up ℤ)).app K))) =
      DerivedCategory.Qh.map (((forget₂ (ModuleCat.{u + 1} Λ)
          AddCommGrpCat.{u + 1}).mapHomotopyCategory (.up ℤ)).map
            ((HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
              (globalSectionsUpperStarNatTrans (ModuleCat.{u + 1} Λ) f) (.up ℤ)).app K))) ≫
        (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategoryFactorsh.inv.app
          (((Sheaf.Γ X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomotopyCategory (.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj
              (((f)^*[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (.up ℤ) |>.obj K))) :=
    ((forget₂ (ModuleCat.{u + 1} Λ)
      AddCommGrpCat.{u + 1}).mapDerivedCategoryFactorsh.inv.naturality _).symm
  have h7 := (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerivedFunctorUnit.naturality
    ((NatTrans.mapHomotopyCategory (moduleAbelianUpperStarIso Λ f).inv (.up ℤ)).app
      ((HomotopyCategory.quotient _ _).obj K))
  have h8 := forget_mapHomologicalComplex_globalSectionsUpperStarNatTrans Λ f K
  dsimp only [Functor.comp_map, Functor.comp_obj] at h5 h6 h7
  rw [reassoc_of% h2, h4]
  erw [reassoc_of% h1']
  have h1m :=
    congrArg (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory.map h1
  simp only [Functor.map_comp] at h1m
  rw [reassoc_of% h1m, reassoc_of% h5, reassoc_of% h6]
  erw [reassoc_of% h2']
  have h3' := congrArg (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map h3
  simp only [Functor.map_comp] at h3'
  unfold mapDerivedUpperStarForgetIso
  erw [h3', ← reassoc_of% h7]
  have key := congrArg (HomotopyCategory.quotient AddCommGrpCat.{u + 1} (.up ℤ)).map h8
  simp only [Functor.map_comp] at key
  have key' := congrArg DerivedCategory.Qh.map key
  simp only [Functor.map_comp] at key'
  erw [reassoc_of% key']
  rfl

-- The square of `globalSectionsRestriction_forget` at a K-injective complex.
private lemma globalSectionsRestriction_forget_of_isKInjective {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : CochainComplex (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) [K.IsKInjective] :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory.map
        (globalSectionsRestriction f
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) ≫
      (rightDerivedGlobalSectionsForget Λ X).app
        (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
        ((mapDerivedUpperStarForgetIso Λ f).inv.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) =
    (rightDerivedGlobalSectionsForget Λ Y).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) ≫
      globalSectionsRestriction f ((moduleAbelianForget Λ Y).mapDerivedCategory.obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K))) := by
  rw [← cancel_epi ((forget₂ (ModuleCat.{u + 1} Λ)
    AddCommGrpCat.{u + 1}).mapDerivedCategoryFactorsh.inv.app
      (((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapHomotopyCategory (.up ℤ)).obj
        ((HomotopyCategory.quotient _ _).obj K)) ≫
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory.map
      ((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ _).obj K)))]
  simpa only [Category.assoc] using globalSectionsRestriction_forget_unit Λ f K

/-- **The restriction maps of derived global sections commute with forgetting the module
structure**: for `f : X ⟶ Y` and `M ∈ D(Y_ét, Λ)`, the square
```
RΓ(Y, M) ──────────────────────▶ RΓ(X, f^* M)
    │                                  │
    ▼                                  ▼
RΓ(Y, S_Y M) ──▶ RΓ(X, f^* S_Y M) ≅ RΓ(X, S_X f^* M)
```
of complexes of abelian groups commutes. -/
theorem globalSectionsRestriction_forget {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory.map
        (globalSectionsRestriction f M) ≫
      (rightDerivedGlobalSectionsForget Λ X).app
        (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.obj M) ≫
      (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
        ((mapDerivedUpperStarForgetIso Λ f).inv.app M) =
    (rightDerivedGlobalSectionsForget Λ Y).app M ≫
      globalSectionsRestriction f ((moduleAbelianForget Λ Y).mapDerivedCategory.obj M) := by
  obtain ⟨I, _, ⟨φ⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective M
  let ψ : M ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) :=
    φ ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm
  have hI := globalSectionsRestriction_forget_of_isKInjective Λ f I
  have h₁ := globalSectionsRestriction_naturality f ψ.hom
  have h₂ := (rightDerivedGlobalSectionsForget Λ X).naturality
    (((f)^*[ModuleCat.{u + 1} Λ]).mapDerivedCategory.map ψ.hom)
  have h₃ := (mapDerivedUpperStarForgetIso Λ f).inv.naturality ψ.hom
  have h₄ := (rightDerivedGlobalSectionsForget Λ Y).naturality ψ.hom
  have h₅ := globalSectionsRestriction_naturality f
    ((moduleAbelianForget Λ Y).mapDerivedCategory.map ψ.hom)
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₂ h₃ h₄
  rw [← cancel_mono ((rightDerivedGlobalSections AddCommGrpCat.{u + 1} X).map
    (((f)^*[AddCommGrpCat.{u + 1}]).mapDerivedCategory.map
      ((moduleAbelianForget Λ Y).mapDerivedCategory.map ψ.hom)))]
  simp only [Category.assoc]
  rw [← Functor.map_comp (rightDerivedGlobalSections AddCommGrpCat.{u + 1} X)
    ((mapDerivedUpperStarForgetIso Λ f).inv.app M), ← h₃, Functor.map_comp, ← reassoc_of% h₂,
    ← Functor.map_comp_assoc
      (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).mapDerivedCategory
      (globalSectionsRestriction f M), ← h₁, Functor.map_comp_assoc, ← h₅, ← reassoc_of% h₄, hI]

end AlgebraicGeometry.Etale
