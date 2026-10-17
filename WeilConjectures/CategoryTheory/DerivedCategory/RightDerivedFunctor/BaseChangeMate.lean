/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# The derived base change morphism on K-injective complexes

Consider adjunctions `adj : fU ⊣ fL` and `adj' : f'U ⊣ f'L` of additive functors between abelian
categories with exact left adjoints, and exact functors `gU`, `g'U` forming a square
```
CY ──fU──▶ CX
│          │
gU         g'U
▼          ▼
CY' ─f'U─▶ CX'
```
with an isomorphism `σ : gU ⋙ f'U ≅ fU ⋙ g'U`. In the application the categories are sheaf
categories, `fU ⊣ fL` and `f'U ⊣ f'L` are `f^* ⊣ f_*` and `f'^* ⊣ f'_*` for a cartesian square of
schemes, and `gU`, `g'U` are the pullbacks along the two other sides.

The *derived base change morphism* `R(fL) ⋙ D(gU) ⟶ D(g'U) ⋙ R(f'L)`
(`CategoryTheory.Adjunction.derivedBaseChange`) is the mate of the isomorphism
`D(gU) ⋙ D(f'U) ≅ D(fU) ⋙ D(g'U)` induced by `σ`, under the derived adjunctions
`D(fU) ⊣ R(fL)` and `D(f'U) ⊣ R(f'L)`. The *underived base change morphism*
`fL ⋙ gU ⟶ g'U ⋙ f'L` is the mate of `σ` itself.

On the image of a complex `K`, the derived base change morphism is computed by the underived one
(`CategoryTheory.Adjunction.derivedBaseChange_app_fac`):
```
D(gU)(Q fL K) ──D(gU)(unit)──▶ D(gU)(R(fL) K) ──β──▶ R(f'L)(D(g'U) K)
     │                                                     │
     ≅                                                     ≅
     ▼                                                     ▼
Q(gU fL K) ──Q(underived)──▶ Q(f'L g'U K) ──unit──▶ R(f'L)(Q(g'U K))
```
Consequently, if `K` is K-injective and `q : g'U K ⟶ J` is a quasi-isomorphism to a K-injective
complex, the derived base change morphism is an isomorphism at `K` if and only if the morphism
of complexes `gU (fL K) ⟶ f'L (g'U K) ⟶ f'L J` is a quasi-isomorphism
(`CategoryTheory.Adjunction.isIso_derivedBaseChange_app_iff`). This is the classical definition
of the base change morphism through K-injective resolutions.
-/

@[expose] public section

open CategoryTheory Limits Abelian

namespace CategoryTheory.Adjunction

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

variable {CY CX CY' CX' : Type*} [Category CY] [Category CX] [Category CY'] [Category CX']
  [Abelian CY] [Abelian CX] [Abelian CY'] [Abelian CX']
  [HasDerivedCategory CY] [HasDerivedCategory CX] [HasDerivedCategory CY']
  [HasDerivedCategory CX'] [HasKInjectiveResolutions CX] [HasKInjectiveResolutions CX']
  {fU : CY ⥤ CX} {fL : CX ⥤ CY} {f'U : CY' ⥤ CX'} {f'L : CX' ⥤ CY'}
  {gU : CY ⥤ CY'} {g'U : CX ⥤ CX'}
  [fU.Additive] [fL.Additive] [f'U.Additive] [f'L.Additive] [gU.Additive] [g'U.Additive]
  [PreservesFiniteLimits fU] [PreservesFiniteColimits fU]
  [PreservesFiniteLimits f'U] [PreservesFiniteColimits f'U]
  [PreservesFiniteLimits gU] [PreservesFiniteColimits gU]
  [PreservesFiniteLimits g'U] [PreservesFiniteColimits g'U]
  (adj : fU ⊣ fL) (adj' : f'U ⊣ f'L) (σ : gU ⋙ f'U ≅ fU ⋙ g'U)

/-- The isomorphism `D(gU) ⋙ D(f'U) ≅ D(fU) ⋙ D(g'U)` of functors on the derived categories
induced by an isomorphism `σ : gU ⋙ f'U ≅ fU ⋙ g'U` of exact functors. -/
noncomputable def mapDerivedCategorySquareIso :
    gU.mapDerivedCategory ⋙ f'U.mapDerivedCategory ≅
      fU.mapDerivedCategory ⋙ g'U.mapDerivedCategory :=
  (Functor.mapDerivedCategoryCompIso gU f'U).symm ≪≫ Functor.mapDerivedCategoryNatIso σ ≪≫
    Functor.mapDerivedCategoryCompIso fU g'U

/-- The underived base change morphism `fL ⋙ gU ⟶ g'U ⋙ f'L`: the mate of `σ` under `fU ⊣ fL`
and `f'U ⊣ f'L`. -/
noncomputable def baseChange : TwoSquare fL g'U gU f'L :=
  mateEquiv adj adj' (TwoSquare.mk _ _ _ _ σ.hom)

/-- The components of a mate `mateEquiv adj₁ adj₂ α`. -/
lemma mateEquiv_natTrans_app {C D E F : Type*} [Category C] [Category D] [Category E]
    [Category F] {G : C ⥤ E} {H : D ⥤ F} {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F}
    {R₂ : F ⥤ E} (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (α : TwoSquare G L₁ L₂ H) (d : D) :
    (mateEquiv adj₁ adj₂ α).natTrans.app d = adj₂.unit.app (G.obj (R₁.obj d)) ≫
      R₂.map (α.natTrans.app (R₁.obj d)) ≫ R₂.map (H.map (adj₁.counit.app d)) := by
  simp [mateEquiv]

/-- The isomorphism `D(gU) ⋙ D(f'U) ≅ D(fU) ⋙ D(g'U)` induced by `σ` is compatible with the
factorizations of the exact functors through the localization functors `Qh`. -/
@[reassoc]
lemma mapDerivedCategorySquareIso_hom_app_fach (Z : HomotopyCategory CY (.up ℤ)) :
    (mapDerivedCategorySquareIso σ).hom.app (DerivedCategory.Qh.obj Z) ≫
      g'U.mapDerivedCategory.map (fU.mapDerivedCategoryFactorsh.hom.app Z) ≫
      g'U.mapDerivedCategoryFactorsh.hom.app ((fU.mapHomotopyCategory _).obj Z) =
    f'U.mapDerivedCategory.map (gU.mapDerivedCategoryFactorsh.hom.app Z) ≫
      f'U.mapDerivedCategoryFactorsh.hom.app ((gU.mapHomotopyCategory _).obj Z) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory σ.hom _).app Z) := by
  have h₁ := Functor.mapDerivedCategoryCompIso_fach fU g'U Z
  have h₂ := Functor.mapDerivedCategoryCompIso_fach gU f'U Z
  rw [Functor.mapHomotopyCategoryCompIso_refl_hom_app] at h₁ h₂
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h₁
  erw [CategoryTheory.Functor.map_id, Category.comp_id] at h₂
  simp only [mapDerivedCategorySquareIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Category.assoc]
  erw [h₁, Functor.mapDerivedCategoryNatIso_fach, ← h₂]
  simp

/-- The derived base change morphism `R(fL) ⋙ D(gU) ⟶ D(g'U) ⋙ R(f'L)`: the mate of the
isomorphism `D(gU) ⋙ D(f'U) ≅ D(fU) ⋙ D(g'U)` induced by `σ`, under the derived adjunctions
`D(fU) ⊣ R(fL)` and `D(f'U) ⊣ R(f'L)`. -/
noncomputable def derivedBaseChange :
    TwoSquare fL.rightDerivedFunctor g'U.mapDerivedCategory gU.mapDerivedCategory
      f'L.rightDerivedFunctor :=
  mateEquiv adj.mapDerivedCategoryRightDerivedAdjunction
    adj'.mapDerivedCategoryRightDerivedAdjunction
    (TwoSquare.mk _ _ _ _ (mapDerivedCategorySquareIso σ).hom)

/-- **The derived base change morphism on the image of a complex** is computed by the underived
base change morphism, through the units of the right derived functors and the factorizations of
the exact functors through the localization functors. -/
lemma derivedBaseChange_app_fac (K : CochainComplex CX ℤ) :
    gU.mapDerivedCategory.map
        (fL.rightDerivedFunctorUnit.app ((HomotopyCategory.quotient _ _).obj K)) ≫
      (derivedBaseChange adj adj' σ).natTrans.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) ≫
      f'L.rightDerivedFunctor.map
        (g'U.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.quotient _ _).obj K)) =
    gU.mapDerivedCategoryFactorsh.hom.app
        ((fL.mapHomotopyCategory _).obj ((HomotopyCategory.quotient _ _).obj K)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (baseChange adj adj' σ).natTrans _).app K)) ≫
      f'L.rightDerivedFunctorUnit.app
        ((g'U.mapHomotopyCategory _).obj ((HomotopyCategory.quotient _ _).obj K)) := by
  let X := (HomotopyCategory.quotient CX (.up ℤ)).obj K
  let Z := (fL.mapHomotopyCategory (.up ℤ)).obj X
  let N := (gU.mapHomotopyCategory (.up ℤ)).obj Z
  let c := (adj.mapHomotopyCategory (.up ℤ)).counit.app X
  let m := (NatTrans.mapHomotopyCategory σ.hom (.up ℤ)).app Z ≫
    (g'U.mapHomotopyCategory (.up ℤ)).map c
  have hε : fU.mapDerivedCategory.map (fL.rightDerivedFunctorUnit.app X) ≫
      adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Qh.obj X) =
        fU.mapDerivedCategoryFactorsh.hom.app Z ≫ DerivedCategory.Qh.map c :=
    (adj.mapHomotopyCategory (.up ℤ)).derivedε_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
      fU.mapDerivedCategoryFactorsh.hom fL.rightDerivedFunctorUnit X
  have hη : adj'.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj N) ≫
      f'L.rightDerivedFunctor.map (f'U.mapDerivedCategoryFactorsh.hom.app N) =
        DerivedCategory.Qh.map ((adj'.mapHomotopyCategory (.up ℤ)).unit.app N) ≫
          f'L.rightDerivedFunctorUnit.app ((f'U.mapHomotopyCategory (.up ℤ)).obj N) :=
    (adj'.mapHomotopyCategory (.up ℤ)).derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
      f'U.mapDerivedCategoryFactorsh.hom f'L.rightDerivedFunctorUnit N
  have hinner : f'U.mapDerivedCategory.map (gU.mapDerivedCategory.map
        (fL.rightDerivedFunctorUnit.app X)) ≫
      (mapDerivedCategorySquareIso σ).hom.app
        (fL.rightDerivedFunctor.obj (DerivedCategory.Qh.obj X)) ≫
      g'U.mapDerivedCategory.map
        (adj.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Qh.obj X)) ≫
      g'U.mapDerivedCategoryFactorsh.hom.app X =
    f'U.mapDerivedCategory.map (gU.mapDerivedCategoryFactorsh.hom.app Z) ≫
      f'U.mapDerivedCategoryFactorsh.hom.app N ≫ DerivedCategory.Qh.map m := by
    erw [(mapDerivedCategorySquareIso σ).hom.naturality_assoc]
    rw [Functor.comp_map, ← Functor.map_comp_assoc, hε, Functor.map_comp, Category.assoc]
    erw [g'U.mapDerivedCategoryFactorsh.hom.naturality c]
    erw [mapDerivedCategorySquareIso_hom_app_fach_assoc]
    simp [m]
  have hK : (HomotopyCategory.quotient _ _).map
        ((NatTrans.mapHomologicalComplex (baseChange adj adj' σ).natTrans _).app K) =
      (adj'.mapHomotopyCategory (.up ℤ)).unit.app N ≫
        (f'L.mapHomotopyCategory (.up ℤ)).map m := by
    sorry
  rw [derivedBaseChange, mateEquiv_natTrans_app]
  simp only [Category.assoc]
  erw [adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality_assoc]
  rw [← f'L.rightDerivedFunctor.map_comp, ← f'L.rightDerivedFunctor.map_comp,
    ← f'L.rightDerivedFunctor.map_comp]
  erw [hinner]
  simp only [Functor.map_comp]
  erw [← adj'.mapDerivedCategoryRightDerivedAdjunction.unit.naturality_assoc]
  erw [reassoc_of% hη]
  erw [← f'L.rightDerivedFunctorUnit.naturality m]
  rw [hK, Functor.map_comp, Category.assoc]
  rfl

/-- **The derived base change morphism through K-injective resolutions.** For a K-injective
complex `K` and a quasi-isomorphism `q : g'U K ⟶ J` to a K-injective complex, the derived base
change morphism is an isomorphism at `K` if and only if the morphism of complexes
`gU (fL K) ⟶ f'L (g'U K) ⟶ f'L J` (the underived base change morphism followed by `f'L q`) is a
quasi-isomorphism. -/
lemma isIso_derivedBaseChange_app_iff (K : CochainComplex CX ℤ) [K.IsKInjective]
    (J : CochainComplex CX' ℤ) [J.IsKInjective]
    (q : (g'U.mapHomologicalComplex _).obj K ⟶ J) [QuasiIso q] :
    IsIso ((derivedBaseChange adj adj' σ).natTrans.app (DerivedCategory.Q.obj K)) ↔
      IsIso (DerivedCategory.Q.map
        ((NatTrans.mapHomologicalComplex (baseChange adj adj' σ).natTrans _).app K ≫
          (f'L.mapHomologicalComplex _).map q)) := by
  sorry

end CategoryTheory.Adjunction
