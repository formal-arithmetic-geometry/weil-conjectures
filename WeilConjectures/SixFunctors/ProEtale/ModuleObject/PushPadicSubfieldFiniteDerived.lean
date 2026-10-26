/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Products
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsFlat
public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalarsUnit
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ScalarExtension
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.PushPadicSubfieldFinite

/-!
# Derived pushforward commutes with `F ⊗_E -` for finite subextensions `E ≤ F`

Let `ℓ` be a prime, `E ≤ F` finite subextensions of `ℚ̄_ℓ / ℚ_ℓ` and `f : X ⟶ Y` any morphism of
schemes. The derived comparison **(Push)** `F_Y ⊗ᴸ Rf_* K ⟶ Rf_*(F_X ⊗ᴸ K)` for the inclusion
`E̲ ⟶ F̲` is an isomorphism for every `K ∈ D(E_X)`, without boundedness assumptions
(`ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjMap_app`, blueprint
`lem-sfb-subfield-push-iso`).

Represent `K` by a K-injective complex `I`. By `ProEtale.CondensedRing.derivedPushHom_app_Qh_fac`
the derived (Push) at `I` is identified with the underived one, which is an isomorphism
(`ProEtale.CondensedRing.isIso_pushHom_padicSubfieldRingObjMap_app`), through the units of
`Rf_*` at `I` and at `F_X ⊗ I`. The former is an isomorphism since `I` is K-injective. For the
latter, restriction of scalars to `E_Y` reflects isomorphisms and identifies it with the unit of
`Rf_*` for `E`-coefficients at the restriction of scalars of `F_X ⊗ I`. Choosing a basis
`b₁, …, bₙ` of `F` over `E`, this complex is isomorphic to `Iⁿ` through the `E_X`-linear maps
`m ↦ bᵢ • (1 ⊗ m)` (`CategoryTheory.Mod.isIso_biproductDesc_extendUnitGlobalSmul`), hence is
K-injective (`CochainComplex.isKInjective_mapHomologicalComplex_obj_of_isIso_biproductDesc`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits MonoidalCategory MonObj

namespace CategoryTheory.Mod

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C] {A : C} [MonObj A]
  [IsCommMonObj A]

/-- The action of a global section of a commutative monoid object `A` on an `A`-module is
`A`-linear. -/
lemma isModHom_globalSmul (σ : 𝟙_ C ⟶ A) (M : Mod C A) : IsModHom A (globalSmul σ M) where
  smul_hom := by
    have h : (ρ_ A).inv ≫ A ◁ σ ≫ μ[A] = (λ_ A).inv ≫ σ ▷ A ≫ μ[A] := by
      conv_lhs => rw [← IsCommMonObj.mul_comm A]
      rw [BraidedCategory.braiding_naturality_right_assoc, rightUnitor_inv_braiding_assoc]
    have h₁ : (λ_ (A ⊗ M.X)).inv ≫ σ ▷ (A ⊗ M.X) ≫ (α_ A A M.X).inv =
        ((λ_ A).inv ≫ σ ▷ A) ▷ M.X := by
      monoidal
    have h₂ : A ◁ (λ_ M.X).inv ≫ A ◁ σ ▷ M.X ≫ (α_ A A M.X).inv =
        ((ρ_ A).inv ≫ A ◁ σ) ▷ M.X := by
      monoidal
    rw [globalSmul, MonoidalCategory.selfLeftAction_actionHomRight]
    erw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, ModObj.mul_smul_self_flip,
      reassoc_of% h₁]
    simp only [MonoidalCategory.whiskerLeft_comp, Category.assoc]
    erw [ModObj.mul_smul_self_flip, reassoc_of% h₂]
    rw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc, Category.assoc, Category.assoc, h]

/-- The action of a global section `σ` of a commutative monoid object `A` on an `A`-module `M`,
as an endomorphism of `A`-modules. -/
noncomputable def globalSmulHom (σ : 𝟙_ C ⟶ A) (M : Mod C A) : M ⟶ M :=
  have := isModHom_globalSmul σ M
  ⟨globalSmul σ M⟩

@[simp]
lemma globalSmulHom_hom (σ : 𝟙_ C ⟶ A) (M : Mod C A) :
    (globalSmulHom σ M).hom = globalSmul σ M :=
  rfl

/-- The action of a global section is natural. -/
@[reassoc]
lemma globalSmulHom_naturality (σ : 𝟙_ C ⟶ A) {M N : Mod C A} (g : M ⟶ N) :
    globalSmulHom σ M ≫ g = g ≫ globalSmulHom σ N :=
  Hom.ext (globalSmul_comp_hom g σ)

end CategoryTheory.Mod

namespace CategoryTheory.Mod

attribute [local instance] Abelian.hasFiniteBiproducts

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] [IsGrothendieckAbelian.{v} C]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R] [IsCommMonObj S] (φ : R ⟶ S) [IsMonHom φ]

/-- The `R`-linear map `M ⟶ S ⊗_R M`, `m ↦ σ • (1 ⊗ m)`, for a global section `σ` of `S`,
natural in the `R`-module `M`. -/
noncomputable def extendUnitGlobalSmul (σ : 𝟙_ C ⟶ S) :
    𝟭 (Mod C R) ⟶ extendScalars φ ⋙ comap φ where
  app M := (extendRestrictAdjunction φ).unit.app M ≫
    (comap φ).map (globalSmulHom σ ((extendScalars φ).obj M))
  naturality M N g := by
    rw [Functor.comp_map, Category.assoc, ← Functor.map_comp, globalSmulHom_naturality,
      Functor.map_comp]
    exact (extendRestrictAdjunction φ).unit.naturality_assoc g _

omit [MonoidalPreadditive C] in
/-- The underlying morphism of `extendUnitGlobalSmul` is `m ↦ σ • (1 ⊗ m)`. -/
@[simp]
lemma extendUnitGlobalSmul_app_hom (σ : 𝟙_ C ⟶ S) (M : Mod C R) :
    ((extendUnitGlobalSmul φ σ).app M).hom =
      extendUnitHom φ M ≫ globalSmul σ (extendScalarsObj φ M) := by
  dsimp only [extendUnitGlobalSmul]
  rw [comp_hom', extendRestrictAdjunction_unit_app_hom]
  rfl

/-- **Extension of scalars along a finite free algebra, linearly**: if global sections
`s₁, …, sₙ` of `S` form a basis of `S` over `R`, then the `R`-linear map `Mⁿ ⟶ S ⊗_R M`,
`(mᵢ) ↦ ∑ sᵢ • (1 ⊗ mᵢ)`, is an isomorphism for every `R`-module object `M`. -/
theorem isIso_biproductDesc_extendUnitGlobalSmul {n : ℕ} (s : Fin n → (𝟙_ C ⟶ S))
    (hs : IsIso (biproduct.desc fun i ↦ φ ≫ globalSmul (s i) (regular S) :
      ⨁ (fun _ : Fin n ↦ R) ⟶ S))
    (M : Mod C R) :
    IsIso (biproduct.desc fun i ↦ (extendUnitGlobalSmul φ (s i)).app M :
      ⨁ (fun _ : Fin n ↦ M) ⟶ (comap φ).obj ((extendScalars φ).obj M)) := by
  have hX := isIso_biproductDesc_extendUnitHom_globalSmul φ s hs M
  have : IsIso ((forget R).map (biproduct.desc fun i ↦ (extendUnitGlobalSmul φ (s i)).app M :
      ⨁ (fun _ : Fin n ↦ M) ⟶ (comap φ).obj ((extendScalars φ).obj M))) := by
    rw [← biproduct.mapBiproduct_hom_desc]
    have e : (fun i ↦ (forget R).map ((extendUnitGlobalSmul φ (s i)).app M)) =
        fun i ↦ extendUnitHom φ M ≫ globalSmul (s i) (extendScalarsObj φ M) :=
      funext fun i ↦ extendUnitGlobalSmul_app_hom φ (s i) M
    rw [e]
    exact IsIso.comp_isIso' inferInstance hX
  exact isIso_of_reflects_iso _ (forget R)

end CategoryTheory.Mod

namespace CochainComplex

attribute [local instance] Abelian.hasFiniteBiproducts

variable {A : Type*} [Category* A] [Abelian A]

/-- Let `G` be an additive endofunctor of an abelian category, together with natural
transformations `uᵢ : 𝟭 ⟶ G` (`i < n`) such that `(uᵢ)ᵢ : Mⁿ ⟶ G M` is an isomorphism for every
`M`. Then `G` preserves K-injective complexes, `G I` being isomorphic to `Iⁿ`. -/
lemma isKInjective_mapHomologicalComplex_obj_of_isIso_biproductDesc (G : A ⥤ A) [G.Additive]
    {n : ℕ} (u : Fin n → (𝟭 A ⟶ G))
    (hu : ∀ M, IsIso (biproduct.desc fun i ↦ (u i).app M : ⨁ (fun _ : Fin n ↦ M) ⟶ G.obj M))
    (I : CochainComplex A ℤ) [I.IsKInjective] :
    IsKInjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := by
  let g : Fin n → (I ⟶ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) := fun i ↦
    { f k := (u i).app (I.X k)
      comm' _ _ _ := ((u i).naturality _).symm }
  have (k : ℤ) : IsIso ((biproduct.desc g).f k) := by
    have e := biproduct.mapBiproduct_hom_desc
      (F := HomologicalComplex.eval A (ComplexShape.up ℤ) k) (g := g)
    have := hu (I.X k)
    have : IsIso ((HomologicalComplex.eval A (ComplexShape.up ℤ) k).map (biproduct.desc g)) := by
      rw [← e]
      exact IsIso.comp_isIso' inferInstance this
    exact this
  have : IsIso (biproduct.desc g) := HomologicalComplex.Hom.isIso_of_components _
  have : IsKInjective (⨁ fun _ : Fin n ↦ I) := isKInjective_of_isLimitFan (biproduct.isLimit _)
  exact isKInjective_of_iso (asIso (biproduct.desc g))

end CochainComplex

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

open scoped CategoryTheory.Obj

variable (ℓ : ℕ) [Fact ℓ.Prime] {E F : PadicAlgCl.FiniteIntermediateField ℓ} (hF : E ≤ F)
  {X Y : Scheme.{u}} (f : X ⟶ Y)

set_option maxHeartbeats 1000000 in
-- Unifying the various forms of the restricted complexes is slow.
/-- For a finite extension `E ≤ F` and a K-injective complex `I` of `E_X`-modules, the unit of
`Rf_*` for `F`-coefficients is an isomorphism at `F_X ⊗_{E_X} I`. Indeed restriction of scalars
to `E_Y` reflects isomorphisms, and carries it to the unit of `Rf_*` for `E`-coefficients at the
restriction of scalars of `F_X ⊗_{E_X} I`, which is isomorphic to `Iⁿ` for `n = [F : E]`, hence
K-injective. -/
lemma isIso_rightDerivedFunctorUnit_app_extendScalars_padicSubfieldRingObjMap
    (I : CochainComplex (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E)) ℤ) [I.IsKInjective] :
    IsIso (((f)_*⟦Profinite.continuousMapRingObj F⟧).rightDerivedFunctorUnit.app
      (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).mapHomotopyCategory _).obj
        ((HomotopyCategory.quotient _ _).obj I))) := by
  obtain ⟨n, b, h⟩ :=
    Profinite.exists_isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul.{u} ℓ hF
  have : CochainComplex.IsKInjective (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF) ⋙
      Mod.comap (padicSubfieldRingObjMap X ℓ hF)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_mapHomologicalComplex_obj_of_isIso_biproductDesc _
      (fun i ↦ Mod.extendUnitGlobalSmul _ (padicSubfieldConstSection ℓ X (b i)))
      (Mod.isIso_biproductDesc_extendUnitGlobalSmul _ _
        (isIso_biproductDesc_padicSubfieldRingObjMap_globalSmul X ℓ hF b h)) I
  have hE : IsIso (((f)_*⟦Profinite.continuousMapRingObj E⟧).rightDerivedFunctorUnit.app
      ((HomotopyCategory.quotient _ _).obj (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF) ⋙
        Mod.comap (padicSubfieldRingObjMap X ℓ hF)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))) :=
    inferInstance
  have hc : IsIso (NatTrans.mapHomotopyCategory
      (comapLowerStarIso (Profinite.padicSubfieldRingObjMap ℓ hF) f).hom (ComplexShape.up ℤ)) :=
    ⟨NatTrans.mapHomotopyCategory
      (comapLowerStarIso (Profinite.padicSubfieldRingObjMap ℓ hF) f).inv (ComplexShape.up ℤ), by
      rw [← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id, NatTrans.mapHomotopyCategory_id],
      by rw [← NatTrans.mapHomotopyCategory_comp, Iso.inv_hom_id,
        NatTrans.mapHomotopyCategory_id]⟩
  have hfac := derivedComapLowerStarIso_hom_app_Qh (Profinite.padicSubfieldRingObjMap ℓ hF) f
    (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).mapHomotopyCategory _).obj
      ((HomotopyCategory.quotient _ _).obj I))
  have : IsIso ((Mod.comap (padicSubfieldRingObjMap Y ℓ hF)).mapDerivedCategory.map
      (((f)_*⟦Profinite.continuousMapRingObj F⟧).rightDerivedFunctorUnit.app
        (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).mapHomotopyCategory _).obj
          ((HomotopyCategory.quotient _ _).obj I)))) := by
    have : IsIso ((Mod.comap (padicSubfieldRingObjMap Y ℓ hF)).mapDerivedCategory.map
        (((f)_*⟦Profinite.continuousMapRingObj F⟧).rightDerivedFunctorUnit.app
          (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).mapHomotopyCategory _).obj
            ((HomotopyCategory.quotient _ _).obj I))) ≫
        (derivedComapLowerStarIso (Profinite.padicSubfieldRingObjMap ℓ hF) f).hom.app _) := by
      erw [hfac]
      have : IsIso (((f)_*⟦Profinite.continuousMapRingObj E⟧).rightDerivedFunctorUnit.app
          (((Mod.comap (padicSubfieldRingObjMap X ℓ hF)).mapHomotopyCategory _).obj
            (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).mapHomotopyCategory _).obj
              ((HomotopyCategory.quotient _ _).obj I)))) := hE
      have : IsIso ((NatTrans.mapHomotopyCategory
          (comapLowerStarIso (Profinite.padicSubfieldRingObjMap ℓ hF) f).hom
            (ComplexShape.up ℤ)).app
          (((Mod.extendScalars (padicSubfieldRingObjMap X ℓ hF)).mapHomotopyCategory _).obj
            ((HomotopyCategory.quotient _ _).obj I))) :=
        inferInstance
      exact IsIso.comp_isIso' inferInstance
        (IsIso.comp_isIso' (Functor.map_isIso _ _) (IsIso.comp_isIso' ‹_› inferInstance))
    exact IsIso.of_isIso_comp_right _
      ((derivedComapLowerStarIso (Profinite.padicSubfieldRingObjMap ℓ hF) f).hom.app _)
  exact isIso_of_reflects_iso _ (Mod.comap (padicSubfieldRingObjMap Y ℓ hF)).mapDerivedCategory

set_option maxHeartbeats 1000000 in
-- Producing the K-injective resolution of `K` is slow to elaborate.
/-- **(Push) for `E ⟶ F` on the unbounded derived category** (blueprint
`lem-sfb-subfield-push-iso`): for finite subextensions `E ≤ F` and every morphism of schemes
`f : X ⟶ Y`, the comparison `F_Y ⊗ᴸ Rf_* K ⟶ Rf_*(F_X ⊗ᴸ K)` is an isomorphism for every
`K ∈ D(E_X)`. Represent `K` by a K-injective complex `I`: the derived (Push) at `I` is identified
with the underived one, an isomorphism, through the unit of `Rf_*` at `I` and at `F_X ⊗ I`, both
isomorphisms (`isIso_rightDerivedFunctorUnit_app_extendScalars_padicSubfieldRingObjMap`). -/
theorem isIso_derivedPushHom_padicSubfieldRingObjMap_app
    (K : DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1})
      (padicSubfieldRingObj X ℓ E))) :
    IsIso ((derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ hF) f).app K) := by
  obtain ⟨I, _, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  rw [NatTrans.isIso_app_iff_of_iso _ (e ≪≫ ((DerivedCategory.quotientCompQhIso _).app I).symm)]
  have h := derivedPushHom_app_Qh_fac (Profinite.padicSubfieldRingObjMap ℓ hF) f I
  have : ∀ k, IsIso (((NatTrans.mapHomologicalComplex
      (pushHom (Profinite.padicSubfieldRingObjMap ℓ hF) f) (ComplexShape.up ℤ)).app I).f k) :=
    fun k ↦ isIso_pushHom_padicSubfieldRingObjMap_app ℓ hF f (I.X k)
  have : IsIso ((NatTrans.mapHomologicalComplex
      (pushHom (Profinite.padicSubfieldRingObjMap ℓ hF) f) (ComplexShape.up ℤ)).app I) :=
    HomologicalComplex.Hom.isIso_of_components _
  have : IsIso ((NatTrans.mapHomotopyCategory
      (pushHom (Profinite.padicSubfieldRingObjMap ℓ hF) f) (ComplexShape.up ℤ)).app
        ((HomotopyCategory.quotient _ _).obj I)) :=
    Functor.map_isIso (HomotopyCategory.quotient _ _) ((NatTrans.mapHomologicalComplex
      (pushHom (Profinite.padicSubfieldRingObjMap ℓ hF) f) (ComplexShape.up ℤ)).app I)
  have := isIso_rightDerivedFunctorUnit_app_extendScalars_padicSubfieldRingObjMap ℓ hF f I
  have := IsIso.of_isIso_fac_left h
  exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ _ inferInstance this

/-- **(Push)** is an isomorphism for a finite extension `F/E`, on all unbounded objects
(`ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjMap_app`). -/
instance isIso_derivedPushHom_padicSubfieldRingObjMap :
    IsIso (derivedPushHom (Profinite.padicSubfieldRingObjMap ℓ hF) f) :=
  have := isIso_derivedPushHom_padicSubfieldRingObjMap_app ℓ hF f
  NatIso.isIso_of_isIso_app _

/-- **(Shriek)** is an isomorphism for a finite extension `F/E`, on all unbounded objects. -/
example [HasCompactification f] :
    IsIso (derivedLowerShriekHom (Profinite.padicSubfieldRingObjMap ℓ hF) f) :=
  inferInstance

end AlgebraicGeometry.ProEtale.CondensedRing
