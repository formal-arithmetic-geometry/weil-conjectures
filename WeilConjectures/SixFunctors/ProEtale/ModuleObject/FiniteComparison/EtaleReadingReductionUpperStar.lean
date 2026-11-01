/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateCube
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarRestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.RestrictScalars
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionResMate2

/-!
# The base change map `Res Rν_* ⟶ Rν_* Res` and the pullbacks

Write `Res` for the restriction of scalars along `φ : Λ →+* Λ'` and
`ω : Res Rν_* ⟶ Rν_* Res` for the base change map of `Res` with `Rν_*`
(`ProEtale.derivedRestrictScalarsCompComparisonLowerStarMap`). This file shows:

* `ProEtale.isIso_derivedRestrictScalarsCompComparisonLowerStarMap`: for a surjective `φ` with
  principal kernel, `ω` is an isomorphism, being the conjugate of the commutation
  `ν^* Ψ ≅ Ψ ν^*` of `ν^*` with the derived extensions of scalars;
* `ProEtale.map_app_comp_rightDerivedComparisonBaseChange_app_comp_map_eq`: `ω` is compatible
  with the base change maps `Lg^* Rν_* ⟶ Rν_* Lg^*` (`ProEtale.rightDerivedComparisonBaseChange`)
  and the commutations of `Res` with the derived pullbacks.

Both are used for the reduction square for the pullbacks (blueprint
`det-sp-purity-coefficient-change`).
-/

@[expose] public section

universe u

open CategoryTheory Category Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.Functor

variable {A' A B' B C' C D' D : Type*} [Category A'] [Category A] [Category B'] [Category B]
  [Category C'] [Category C] [Category D'] [Category D] [Abelian A'] [Abelian A] [Abelian B']
  [Abelian B] [Abelian C'] [Abelian C] [Abelian D'] [Abelian D] [HasDerivedCategory A']
  [HasDerivedCategory A] [HasDerivedCategory B'] [HasDerivedCategory B] [HasDerivedCategory C']
  [HasDerivedCategory C] [HasDerivedCategory D'] [HasDerivedCategory D]
  {rA : A' ⥤ A} {rB : B' ⥤ B} {rC : C' ⥤ C} {rD : D' ⥤ D} {νA' : A' ⥤ C'} {νA : A ⥤ C}
  {νB' : B' ⥤ D'} {νB : B ⥤ D} {gA' : A' ⥤ B'} {gA : A ⥤ B} {gC' : C' ⥤ D'} {gC : C ⥤ D}
  [rA.Additive] [PreservesFiniteLimits rA] [PreservesFiniteColimits rA]
  [rB.Additive] [PreservesFiniteLimits rB] [PreservesFiniteColimits rB]
  [rC.Additive] [PreservesFiniteLimits rC] [PreservesFiniteColimits rC]
  [rD.Additive] [PreservesFiniteLimits rD] [PreservesFiniteColimits rD]
  [νA'.Additive] [PreservesFiniteLimits νA'] [PreservesFiniteColimits νA']
  [νA.Additive] [PreservesFiniteLimits νA] [PreservesFiniteColimits νA]
  [νB'.Additive] [PreservesFiniteLimits νB'] [PreservesFiniteColimits νB']
  [νB.Additive] [PreservesFiniteLimits νB] [PreservesFiniteColimits νB]
  [gA'.Additive] [PreservesFiniteLimits gA'] [PreservesFiniteColimits gA']
  [gA.Additive] [PreservesFiniteLimits gA] [PreservesFiniteColimits gA]
  [gC'.Additive] [PreservesFiniteLimits gC'] [PreservesFiniteColimits gC']
  [gC.Additive] [PreservesFiniteLimits gC] [PreservesFiniteColimits gC]

/-- **Cubes of exact functors pass to derived categories**: if the cube formed by six
isomorphisms of composites of exact functors commutes, then so does the cube formed by the
induced isomorphisms `Functor.mapDerivedCategorySquareIso` on derived categories. -/
lemma mapDerivedCategorySquareIso_cube (σA : rA ⋙ νA ≅ νA' ⋙ rC) (σB : rB ⋙ νB ≅ νB' ⋙ rD)
    (τ' : νA' ⋙ gC' ≅ gA' ⋙ νB') (τ : νA ⋙ gC ≅ gA ⋙ νB) (ρE : rA ⋙ gA ≅ gA' ⋙ rB)
    (ρP : rC ⋙ gC ≅ gC' ⋙ rD)
    (h : ∀ X, νB.map (ρE.hom.app X) ≫ σB.hom.app (gA'.obj X) ≫ rD.map (τ'.inv.app X) =
      τ.inv.app (rA.obj X) ≫ gC.map (σA.hom.app X) ≫ ρP.hom.app (νA'.obj X))
    (K : DerivedCategory A') :
    νB.mapDerivedCategory.map ((mapDerivedCategorySquareIso ρE).hom.app K) ≫
      (mapDerivedCategorySquareIso σB).hom.app (gA'.mapDerivedCategory.obj K) ≫
      rD.mapDerivedCategory.map ((mapDerivedCategorySquareIso τ').inv.app K) =
    (mapDerivedCategorySquareIso τ).inv.app (rA.mapDerivedCategory.obj K) ≫
      gC.mapDerivedCategory.map ((mapDerivedCategorySquareIso σA).hom.app K) ≫
      (mapDerivedCategorySquareIso ρP).hom.app (νA'.mapDerivedCategory.obj K) := by
  let α : rA ⋙ gA ⋙ νB ≅ (gA' ⋙ νB') ⋙ rD := isoWhiskerRight ρE νB ≪≫ isoWhiskerLeft gA' σB
  have h₁ := mapDerivedCategorySquareIso_hom_app_comp σA ρP α τ.symm τ'.symm
    (fun X ↦ by simpa [α] using h X) K
  have h₂ := mapDerivedCategorySquareIso_hom_app_comp ρE σB α (Iso.refl _) (Iso.refl _)
    (fun X ↦ by simp [α]) K
  have h₂' : (mapDerivedCategorySquareIso α).hom.app K =
      (mapDerivedCategoryCompIso gA νB).hom.app (rA.mapDerivedCategory.obj K) ≫
        νB.mapDerivedCategory.map ((mapDerivedCategorySquareIso ρE).hom.app K) ≫
        (mapDerivedCategorySquareIso σB).hom.app (gA'.mapDerivedCategory.obj K) ≫
        rD.mapDerivedCategory.map ((mapDerivedCategoryCompIso gA' νB').inv.app K) := by
    rw [← cancel_mono (rD.mapDerivedCategory.map ((mapDerivedCategoryCompIso gA' νB').hom.app K))]
    simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_app]
    simpa [mapDerivedCategoryNatIso_refl] using h₂
  have hτ : (mapDerivedCategorySquareIso τ).inv.app (rA.mapDerivedCategory.obj K) =
      (mapDerivedCategoryCompIso gA νB).inv.app (rA.mapDerivedCategory.obj K) ≫
        (mapDerivedCategoryTriangleIso τ.symm).hom.app (rA.mapDerivedCategory.obj K) := by
    simp [mapDerivedCategoryNatIso_symm]
  have hτ' : (mapDerivedCategorySquareIso τ').inv.app K =
      (mapDerivedCategoryCompIso gA' νB').inv.app K ≫
        (mapDerivedCategoryTriangleIso τ'.symm).hom.app K := by
    simp [mapDerivedCategoryNatIso_symm]
  rw [hτ, hτ', Category.assoc, ← h₁, h₂']
  simp [← Functor.map_comp]


/-- **Cubes of exact functors pass to derived categories, with derived pullbacks**: the variant
of `Functor.mapDerivedCategorySquareIso_cube` where the functors `D(g)` induced by the exact
functors `gA`, `gA'`, `gC`, `gC'` are replaced by isomorphic functors `LgA`, `LgA'`, `LgC`, `LgC'`
(e.g. derived pullbacks), and the isomorphisms of the cube are transported along these
identifications (hypotheses `hT'`, `hT`, `hRE`, `hRP`). -/
lemma mapDerivedCategorySquareIso_cube_of_iso (σA : rA ⋙ νA ≅ νA' ⋙ rC)
    (σB : rB ⋙ νB ≅ νB' ⋙ rD) (τ' : νA' ⋙ gC' ≅ gA' ⋙ νB') (τ : νA ⋙ gC ≅ gA ⋙ νB)
    (ρE : rA ⋙ gA ≅ gA' ⋙ rB) (ρP : rC ⋙ gC ≅ gC' ⋙ rD)
    (h : ∀ X, νB.map (ρE.hom.app X) ≫ σB.hom.app (gA'.obj X) ≫ rD.map (τ'.inv.app X) =
      τ.inv.app (rA.obj X) ≫ gC.map (σA.hom.app X) ≫ ρP.hom.app (νA'.obj X))
    {LgA' : DerivedCategory A' ⥤ DerivedCategory B'} {LgA : DerivedCategory A ⥤ DerivedCategory B}
    {LgC' : DerivedCategory C' ⥤ DerivedCategory D'} {LgC : DerivedCategory C ⥤ DerivedCategory D}
    (eA' : LgA' ≅ gA'.mapDerivedCategory) (eA : LgA ≅ gA.mapDerivedCategory)
    (eC' : LgC' ≅ gC'.mapDerivedCategory) (eC : LgC ≅ gC.mapDerivedCategory)
    (SA : rA.mapDerivedCategory ⋙ νA.mapDerivedCategory ≅
      νA'.mapDerivedCategory ⋙ rC.mapDerivedCategory)
    (hSA : SA = mapDerivedCategorySquareIso σA)
    (SB : rB.mapDerivedCategory ⋙ νB.mapDerivedCategory ≅
      νB'.mapDerivedCategory ⋙ rD.mapDerivedCategory)
    (hSB : SB = mapDerivedCategorySquareIso σB)
    (T' : νA'.mapDerivedCategory ⋙ LgC' ≅ LgA' ⋙ νB'.mapDerivedCategory)
    (hT' : ∀ M, T'.inv.app M = νB'.mapDerivedCategory.map (eA'.hom.app M) ≫
      (mapDerivedCategorySquareIso τ').inv.app M ≫ eC'.inv.app (νA'.mapDerivedCategory.obj M))
    (T : νA.mapDerivedCategory ⋙ LgC ≅ LgA ⋙ νB.mapDerivedCategory)
    (hT : ∀ M, T.inv.app M = νB.mapDerivedCategory.map (eA.hom.app M) ≫
      (mapDerivedCategorySquareIso τ).inv.app M ≫ eC.inv.app (νA.mapDerivedCategory.obj M))
    (RE : rA.mapDerivedCategory ⋙ LgA ≅ LgA' ⋙ rB.mapDerivedCategory)
    (hRE : ∀ M, RE.hom.app M = eA.hom.app (rA.mapDerivedCategory.obj M) ≫
      (mapDerivedCategorySquareIso ρE).hom.app M ≫ rB.mapDerivedCategory.map (eA'.inv.app M))
    (RP : rC.mapDerivedCategory ⋙ LgC ≅ LgC' ⋙ rD.mapDerivedCategory)
    (hRP : ∀ M, RP.hom.app M = eC.hom.app (rC.mapDerivedCategory.obj M) ≫
      (mapDerivedCategorySquareIso ρP).hom.app M ≫ rD.mapDerivedCategory.map (eC'.inv.app M))
    (M : DerivedCategory A') :
    νB.mapDerivedCategory.map (RE.hom.app M) ≫ SB.hom.app (LgA'.obj M) ≫
      rD.mapDerivedCategory.map (T'.inv.app M) =
    T.inv.app (rA.mapDerivedCategory.obj M) ≫ LgC.map (SA.hom.app M) ≫
      RP.hom.app (νA'.mapDerivedCategory.obj M) := by
  subst hSA hSB
  have hn := (mapDerivedCategorySquareIso σB).hom.naturality (eA'.inv.app M)
  have hc : rD.mapDerivedCategory.map (νB'.mapDerivedCategory.map (eA'.inv.app M)) ≫
      rD.mapDerivedCategory.map (νB'.mapDerivedCategory.map (eA'.hom.app M)) = 𝟙 _ := by
    simp [← Functor.map_comp]
  simp only [Functor.comp_map] at hn
  rw [hRE, hT', hT, hRP]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hc, ← eC.inv.naturality_assoc]
  simp only [Functor.comp_obj, Iso.inv_hom_id_app_assoc]
  rw [reassoc_of% (mapDerivedCategorySquareIso_cube σA σB τ' τ ρE ρP h M)]

end CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'}

/-- **The base change map `Res Rν_* ⟶ Rν_* Res` is an isomorphism**: it is the conjugate, under
the composite adjunctions `Ψ ⋙ ν^* ⊣ Rν_* ⋙ Res`, of the isomorphism `ν^* ⋙ Ψ ≅ Ψ ⋙ ν^*`
(`comparisonUpperStarDerivedExtendScalarsIso`). -/
lemma isIso_derivedRestrictScalarsCompComparisonLowerStarMap [IsNoetherianRing Λ]
    (hφ : Function.Surjective φ) {a : Λ} (ha : RingHom.ker φ = Ideal.span {a}) (X : Scheme.{u}) :
    IsIso (derivedRestrictScalarsCompComparisonLowerStarMap φ X) := by
  have hσ : (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom =
      mateEquiv (Etale.derivedExtendScalarsAdjunction hφ ha X)
        (ProEtale.derivedExtendScalarsAdjunction hφ ha X)
        (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).hom := by
    rw [comparisonUpperStarDerivedExtendScalarsIso_hom_eq]
    exact (Equiv.apply_symm_apply _ _).symm
  have h : derivedRestrictScalarsCompComparisonLowerStarMap φ X =
      conjugateEquiv ((Etale.derivedExtendScalarsAdjunction hφ ha X).comp
          (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ') X))
        ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).comp
          (ProEtale.derivedExtendScalarsAdjunction hφ ha X))
        (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).hom := by
    rw [← iterated_mateEquiv_conjugateEquiv, ← hσ]
    rfl
  rw [h]
  infer_instance

variable (φ) {Z Y : Scheme.{u}} (g : Z ⟶ Y)

/-- The components of the inverse of `derivedComparisonUpperStarUpperStarIso`, in terms of the
isomorphism induced on derived categories by `comparisonUpperStarUpperStarIso`. -/
lemma derivedComparisonUpperStarUpperStarIso_inv_app (R : Type (u + 1)) [CommRing R]
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} R))) :
    (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} R) g).inv.app M =
      D(ν^*(Z)[ModuleCat.{u + 1} R]).map
          ((Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) g).hom.app M) ≫
        (Functor.mapDerivedCategorySquareIso
          (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} R) g)).inv.app M ≫
        (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} R) g).inv.app
          ((D(ν^*(Y)[ModuleCat.{u + 1} R])).obj M) := by
  simp [derivedComparisonUpperStarUpperStarIso]

/-- The mate along the adjunctions `g^* ⊣ g_*` of the commutation `g^* Res ≅ Res g^*` of étale
pullback with restriction of scalars is the identity of `g_* Res = Res g_*`. -/
lemma mateEquiv_upperStarLowerStarAdjunction_etaleUpperStarRestrictScalarsIso_hom :
    (mateEquiv (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
      (Etale.upperStarRestrictScalarsIso φ g).hom).natTrans = 𝟙 _ :=
  congrArg TwoSquare.natTrans ((mateEquiv _ _).apply_symm_apply _)

/-- The mate along the restriction–coextension adjunctions of the identity of
`g_* Res = Res g_*` on pro-étale sheaves is the identity of `g_* Coext = Coext g_*`. -/
lemma mateEquiv_restrictCoextendScalarsAdj_lowerStar_id :
    (mateEquiv (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Z) φ)
      (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) φ)).symm
        (TwoSquare.mk _ _ _ _ (𝟙 (sheafCompose (Scheme.ProEt.topology Z)
          (ModuleCat.coextendScalars.{u + 1, u + 1, u + 1} φ) ⋙ (g)_*[ModuleCat.{u + 1} Λ']))) =
      TwoSquare.mk ((g)_*[ModuleCat.{u + 1} Λ']) (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ)
        (Sheaf.restrictScalars (Scheme.ProEt.topology Y) φ) ((g)_*[ModuleCat.{u + 1} Λ]) (𝟙 _) := by
  ext G U : 4
  simp only [Functor.comp_obj, mateEquiv_symm_apply, NatTrans.comp_app, Functor.id_obj,
    Functor.leftUnitor_inv_app, Functor.whiskerRight_app, Functor.comp_map,
    Functor.associator_inv_app, Functor.associator_hom_app, CategoryTheory.Functor.map_id,
    Functor.whiskerLeft_app, Functor.rightUnitor_hom_app, Category.comp_id, Category.id_comp,
    ObjectProperty.FullSubcategory.comp_hom, sheafCompose_map_hom,
    Sheaf.restrictCoextendScalarsAdj_counit_app_hom_app, NatTrans.id_app]
  rw [ProEtale.lowerStar_map_hom_app, Sheaf.restrictCoextendScalarsAdj_unit_app_hom_app]
  exact (ModuleCat.restrictCoextendScalarsAdj.{u + 1} φ).left_triangle_components _

/-- The mate along the adjunctions `g^* ⊣ g_*` of the commutation `g^* Res ≅ Res g^*` of
pro-étale pullback with restriction of scalars is the identity of `g_* Res = Res g_*`. -/
lemma mateEquiv_upperStarLowerStarAdjunction_upperStarRestrictScalarsIso_hom :
    (mateEquiv (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
      (upperStarRestrictScalarsIso φ g).hom).natTrans = 𝟙 _ := by
  have h := iterated_mateEquiv_conjugateEquiv
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
    (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Y) φ)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology Z) φ)
    (upperStarRestrictScalarsIso φ g).hom
  rw [conjugateEquiv_upperStarRestrictScalarsIso_hom] at h
  exact congrArg TwoSquare.natTrans (((Equiv.eq_symm_apply _).2 h).trans
    (mateEquiv_restrictCoextendScalarsAdj_lowerStar_id φ g))

/-- The base change map `g^* ν_* ⟶ ν_* g^*` (the mate of `comparisonUpperStarUpperStarIso`
along `ν^* ⊣ ν_*`) has as mate along `g^* ⊣ g_*` the identity of `ν_* g_* = g_* ν_*`. -/
lemma mateEquiv_mateEquiv_comparisonUpperStarUpperStarIso_inv (A : Type*) [Category.{u + 1} A]
    [Abelian A] [IsGrothendieckAbelian.{u + 1} A] :
    (mateEquiv (ProEtale.upperStarLowerStarAdjunction A g)
      (Etale.upperStarLowerStarAdjunction A g)
      (mateEquiv (comparisonAdjunction A Y) (comparisonAdjunction A Z)
        (comparisonUpperStarUpperStarIso A g).inv)).natTrans = 𝟙 _ := by
  rw [iterated_mateEquiv_conjugateEquiv, comparisonUpperStarUpperStarIso,
    conjugateIsoEquiv_symm_apply_inv, Equiv.apply_symm_apply]
  rfl

/-- **The cube of the commutations of `ν^*`, `Res` and `g^*` on sheaves**: for a sheaf `X` of
`Λ'`-modules on `Y_ét`, the two isomorphisms `ν^*(g^*(Res X)) ≅ Res(g^*(ν^* X))` obtained from
the commutations of `ν^*` with `g^*` (`comparisonUpperStarUpperStarIso`), of `ν^*` with `Res`
(`restrictScalarsCompComparisonUpperStar`) and of `Res` with `g^*` on both sites agree. -/
theorem map_app_comp_restrictScalarsCompComparisonUpperStar_app_comp_map_eq
    (X : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ')) :
    (ν^*(Z)[ModuleCat.{u + 1} Λ]).map ((Etale.upperStarRestrictScalarsIso φ g).hom.app X) ≫
      (restrictScalarsCompComparisonUpperStar φ Z).app
        ((Etale.upperStar (ModuleCat.{u + 1} Λ') g).obj X) ≫
      (Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).map
        ((comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ') g).inv.app X) =
    (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) g).inv.app
        ((Sheaf.restrictScalars Y.smallEtaleTopology φ).obj X) ≫
      (ProEtale.upperStar (ModuleCat.{u + 1} Λ) g).map
        ((restrictScalarsCompComparisonUpperStar φ Y).app X) ≫
      (upperStarRestrictScalarsIso φ g).hom.app ((ν^*(Y)[ModuleCat.{u + 1} Λ']).obj X) := by
  have hres (K : Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ')) :=
    mateEquiv_app_cube_converse (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ') g)
      (ProEtale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
      (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g)
      (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} Λ') Y)
        (comparisonAdjunction (ModuleCat.{u + 1} Λ') Z)
        (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ') g).inv)
      (mateEquiv (comparisonAdjunction (ModuleCat.{u + 1} Λ) Y)
        (comparisonAdjunction (ModuleCat.{u + 1} Λ) Z)
        (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) g).inv)
      (upperStarRestrictScalarsIso φ g).hom (Etale.upperStarRestrictScalarsIso φ g).hom
      (𝟙 _) (𝟙 _) (fun K ↦ ?_) K
  · refine mateEquiv_app_cube_converse (comparisonAdjunction (ModuleCat.{u + 1} Λ') Y)
      (comparisonAdjunction (ModuleCat.{u + 1} Λ') Z) (comparisonAdjunction (ModuleCat.{u + 1} Λ) Y)
      (comparisonAdjunction (ModuleCat.{u + 1} Λ) Z)
      (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ') g).inv
      (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) g).inv
      (restrictScalarsCompComparisonUpperStar φ Y) (restrictScalarsCompComparisonUpperStar φ Z)
      (Etale.upperStarRestrictScalarsIso φ g).hom (upperStarRestrictScalarsIso φ g).hom
      (fun K ↦ ?_) X
    have eY := NatTrans.congr_app
      (mateEquiv_comparisonAdjunction_restrictScalarsCompComparisonUpperStar φ Y) K
    have eZ := NatTrans.congr_app
      (mateEquiv_comparisonAdjunction_restrictScalarsCompComparisonUpperStar φ Z)
      ((ProEtale.upperStar (ModuleCat.{u + 1} Λ') g).obj K)
    have h := hres K
    simp only [NatTrans.id_app] at eY eZ h
    erw [eY, eZ]
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id] at h
    erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
    exact h
  · have e₁ := NatTrans.congr_app
      (mateEquiv_mateEquiv_comparisonUpperStarUpperStarIso_inv g (ModuleCat.{u + 1} Λ')) K
    have e₂ := NatTrans.congr_app
      (mateEquiv_mateEquiv_comparisonUpperStarUpperStarIso_inv g (ModuleCat.{u + 1} Λ))
      ((Sheaf.restrictScalars (Scheme.ProEt.topology Z) φ).obj K)
    have e₃ := NatTrans.congr_app
      (mateEquiv_upperStarLowerStarAdjunction_etaleUpperStarRestrictScalarsIso_hom φ g)
      ((ν_*(Z)[ModuleCat.{u + 1} Λ']).obj K)
    have e₄ := NatTrans.congr_app
      (mateEquiv_upperStarLowerStarAdjunction_upperStarRestrictScalarsIso_hom φ g) K
    simp only [NatTrans.id_app] at e₁ e₂ e₃ e₄
    rw [e₁, e₃, e₄, e₂]
    simp

/-- **The cube of the commutations of `ν^*`, `Res` and `Lg^*`**: for `M` over `Λ'` on `Y_ét`, the
two isomorphisms `ν^*(Lg^*(Res M)) ≅ Res(Lg^*(ν^* M))` obtained from the commutations of `ν^*`
with `Lg^*` (`derivedComparisonUpperStarUpperStarIso`), of `ν^*` with `Res`
(`derivedRestrictScalarsCompComparisonUpperStarIso`) and of `Res` with `Lg^*` on both sites
agree. -/
theorem map_app_comp_derivedRestrictScalarsCompComparisonUpperStarIso_hom_app_comp_map_eq
    (M : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ'))) :
    D(ν^*(Z)[ModuleCat.{u + 1} Λ]).map
        ((Etale.leftDerivedUpperStarRestrictScalarsIso φ g).hom.app M) ≫
      (derivedRestrictScalarsCompComparisonUpperStarIso φ Z).hom.app
        ((L(Etale.upperStar (ModuleCat.{u + 1} Λ') g)).obj M) ≫
      (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z) φ).map
        ((derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ') g).inv.app M) =
    (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) g).inv.app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology φ).obj M) ≫
      (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ) g)).map
        ((derivedRestrictScalarsCompComparisonUpperStarIso φ Y).hom.app M) ≫
      (leftDerivedUpperStarRestrictScalarsIso φ g).hom.app
        ((D(ν^*(Y)[ModuleCat.{u + 1} Λ'])).obj M) :=
  Functor.mapDerivedCategorySquareIso_cube_of_iso
    (asIso (restrictScalarsCompComparisonUpperStar φ Y))
    (asIso (restrictScalarsCompComparisonUpperStar φ Z))
    (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ') g)
    (comparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) g)
    (Etale.upperStarRestrictScalarsIso φ g) (upperStarRestrictScalarsIso φ g)
    (map_app_comp_restrictScalarsCompComparisonUpperStar_app_comp_map_eq φ g)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ') g)
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ') g)
    (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) g)
    (derivedRestrictScalarsCompComparisonUpperStarIso φ Y) rfl
    (derivedRestrictScalarsCompComparisonUpperStarIso φ Z) rfl
    (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ') g)
    (derivedComparisonUpperStarUpperStarIso_inv_app g Λ')
    (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) g)
    (derivedComparisonUpperStarUpperStarIso_inv_app g Λ)
    (Etale.leftDerivedUpperStarRestrictScalarsIso φ g) (fun _ ↦ rfl)
    (leftDerivedUpperStarRestrictScalarsIso φ g) (fun _ ↦ rfl) M

/-- **The base change maps of `Rν_*` with the derived pullbacks commute with the restriction of
scalars**: for `B` over `Λ'` on `Y_proét`, the two morphisms
`Lg^*(Res(Rν_* B)) ⟶ Rν_*(Res(Lg^* B))` obtained from the base change maps
`Lg^* Rν_* ⟶ Rν_* Lg^*` (`rightDerivedComparisonBaseChange`), the base change maps
`Res Rν_* ⟶ Rν_* Res` (`derivedRestrictScalarsCompComparisonLowerStarMap`) and the commutations
of `Res` with `Lg^*` on both sites agree. -/
theorem map_app_comp_rightDerivedComparisonBaseChange_app_comp_map_eq
    (B : DerivedCategory (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} Λ'))) :
    L(Etale.upperStar (ModuleCat.{u + 1} Λ) g).map
        ((derivedRestrictScalarsCompComparisonLowerStarMap φ Y).app B) ≫
      (rightDerivedComparisonBaseChange (ModuleCat.{u + 1} Λ) g).app
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y) φ).obj B) ≫
      R(ν_*(Z)[ModuleCat.{u + 1} Λ]).map
        ((leftDerivedUpperStarRestrictScalarsIso φ g).hom.app B) =
    (Etale.leftDerivedUpperStarRestrictScalarsIso φ g).hom.app
        (R(ν_*(Y)[ModuleCat.{u + 1} Λ']).obj B) ≫
      (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ).map
        ((rightDerivedComparisonBaseChange (ModuleCat.{u + 1} Λ') g).app B) ≫
      (derivedRestrictScalarsCompComparisonLowerStarMap φ Z).app
        (L(ProEtale.upperStar (ModuleCat.{u + 1} Λ') g).obj B) :=
  (mateEquiv_app_cube (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ') Y)
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ') Z)
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Y)
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) Z)
    (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ') g).inv
    (derivedComparisonUpperStarUpperStarIso (ModuleCat.{u + 1} Λ) g).inv
    (derivedRestrictScalarsCompComparisonUpperStarIso φ Y).hom
    (derivedRestrictScalarsCompComparisonUpperStarIso φ Z).hom
    (Etale.leftDerivedUpperStarRestrictScalarsIso φ g).hom
    (leftDerivedUpperStarRestrictScalarsIso φ g).hom
    (map_app_comp_derivedRestrictScalarsCompComparisonUpperStarIso_hom_app_comp_map_eq φ g)
    B).symm

end AlgebraicGeometry.ProEtale
