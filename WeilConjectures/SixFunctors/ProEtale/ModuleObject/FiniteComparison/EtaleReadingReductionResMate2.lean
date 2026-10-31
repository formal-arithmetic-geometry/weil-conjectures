/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.CounitFac

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionResMate

/-!
# The commutation of `ν^*` with the derived extension of scalars is a mate (main statements)

`ProEtale.comparisonUpperStarDerivedExtendScalarsIso_hom_eq` and its consequence
`ProEtale.unit_app_comp_map_derivedExtendScalarsComparisonLowerStarMap_app`, see
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.FiniteComparison.EtaleReadingReductionResMate`.
-/

@[expose] public section

universe u

open CategoryTheory Category Limits MonoidalCategory Abelian

open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- The small étale site of a scheme is essentially small. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {φ : Λ →+* Λ'} (X : Scheme.{u})

variable [IsNoetherianRing Λ] (hφ : Function.Surjective φ) {a : Λ}
  (ha : RingHom.ker φ = Ideal.span {a})

omit [IsNoetherianRing Λ] in
/-- The levelwise identity behind `comparisonUpperStarDerivedExtendScalarsIso_hom_eq`: on the
homotopy category, the unit of extension–restriction of scalars intertwines the commutations of
`ν^*` with extension and with restriction of scalars. -/
lemma mapHomotopyCategory_unit_app_comp_map_comparisonUpperStarCompExtendScalarsIso
    (K : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ℤ) :
    ((Sheaf.extendScalarsAdjunction (Scheme.ProEt.topology X) φ).mapHomotopyCategory
        (ComplexShape.up ℤ)).unit.app
          (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient _ _).obj K)) ≫
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapHomotopyCategory
        (ComplexShape.up ℤ)).map ((Functor.mapHomotopyCategoryCompIso
          (comparisonUpperStarCompExtendScalarsIso φ X) (ComplexShape.up ℤ)).hom.app
            ((HomotopyCategory.quotient _ _).obj K)) =
    ((ν^*(X)[ModuleCat.{u + 1} Λ]).mapHomotopyCategory (ComplexShape.up ℤ)).map
        (((Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).unit.app ((HomotopyCategory.quotient _ _).obj K)) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).hom.app
        (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)) ≫
      (NatTrans.mapHomotopyCategory (restrictScalarsCompComparisonUpperStar φ X)
        (ComplexShape.up ℤ)).app
        (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)) ≫
      (Functor.mapHomotopyCategoryCompIso (Iso.refl _) (ComplexShape.up ℤ)).inv.app
        (((Sheaf.extendScalars X.smallEtaleTopology φ).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)) ≫
      ((Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapHomotopyCategory
        (ComplexShape.up ℤ)).map ((Functor.mapHomotopyCategoryCompIso
          (Iso.refl (Sheaf.extendScalars X.smallEtaleTopology φ ⋙ ν^*(X)[ModuleCat.{u + 1} Λ']))
          (ComplexShape.up ℤ)).hom.app ((HomotopyCategory.quotient _ _).obj K)) := by
  have hu₁ : ((Sheaf.extendScalarsAdjunction (Scheme.ProEt.topology X) φ).mapHomotopyCategory
      (ComplexShape.up ℤ)).unit.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((Sheaf.extendScalarsAdjunction (Scheme.ProEt.topology X) φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app
            (((ν^*(X)[ModuleCat.{u + 1} Λ]).mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) :=
    Adjunction.mapHomotopyCategory_unit_app_quotient _ _ _
  have hu₂ : ((Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ).mapHomotopyCategory
      (ComplexShape.up ℤ)).unit.app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K) =
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ).mapHomologicalComplex
          (ComplexShape.up ℤ)).unit.app K) :=
    Adjunction.mapHomotopyCategory_unit_app_quotient _ _ _
  erw [hu₁, hu₂]
  have hN (M : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) ℤ) :
      (NatTrans.mapHomotopyCategory (restrictScalarsCompComparisonUpperStar φ X)
        (ComplexShape.up ℤ)).app ((HomotopyCategory.quotient _ _).obj M) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
        (restrictScalarsCompComparisonUpperStar φ X) (ComplexShape.up ℤ)).app M) := rfl
  erw [Functor.mapHomotopyCategoryCompIso_hom_app_quotient_obj,
    Functor.mapHomotopyCategoryCompIso_hom_app_quotient_obj, hN,
    Functor.mapHomotopyCategoryCompIso_inv_app_quotient_obj,
    Functor.mapHomotopyCategoryCompIso_hom_app_quotient_obj]
  simp only [Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ (fun n ↦ ?_)
  have h := unit_mateEquiv (Sheaf.extendScalarsAdjunction X.smallEtaleTopology φ)
    (Sheaf.extendScalarsAdjunction (Scheme.ProEt.topology X) φ)
    (comparisonUpperStarCompExtendScalarsIso φ X).hom (K.X n)
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Adjunction.mapHomologicalComplex_unit_app_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplexCompIso_hom_app_f, Functor.mapHomologicalComplexCompIso_inv_app_f,
    Iso.refl_hom, Iso.refl_inv, NatTrans.id_app]
  erw [Category.id_comp, Category.id_comp, CategoryTheory.Functor.map_id, Category.comp_id]
  exact h.symm

/-- **The commutation of `ν^*` with the derived extension of scalars is the mate of the
commutation of `ν^*` with the restriction of scalars**, under the adjunctions `Ψ ⊣ Res`. -/
theorem comparisonUpperStarDerivedExtendScalarsIso_hom_eq :
    (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).hom =
      ((mateEquiv (Etale.derivedExtendScalarsAdjunction hφ ha X)
        (ProEtale.derivedExtendScalarsAdjunction hφ ha X)).symm
          (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom).natTrans := by
  have := Etale.preservesKFlatQuasiIso_extendScalars hφ ha X
  have := ProEtale.preservesKFlatQuasiIso_extendScalars hφ ha X
  refine (Etale.derivedExtendScalars hφ ha X ⋙ D(ν^*(X)[ModuleCat.{u + 1} Λ'])).leftDerived_ext
    (derivedExtendScalarsComparisonUpperStarCounit hφ ha X)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _ _ _ ?_
  have hχ := Functor.leftDerivedNatTrans_fac _ _
    (comparisonUpperStarDerivedExtendScalarsCounit hφ ha X)
    (derivedExtendScalarsComparisonUpperStarCounit hφ ha X)
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) (𝟙 _)
  refine (hχ.trans (Category.comp_id _)).trans ?_
  ext Y
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  apply ((ProEtale.derivedExtendScalarsAdjunction hφ ha X).homEquiv _ _).injective
  rw [homEquiv_comparisonUpperStarDerivedExtendScalarsCounit_app, NatTrans.comp_app,
    Functor.whiskerLeft_app,
    homEquiv_mateEquiv_symm_comp_derivedExtendScalarsComparisonUpperStarCounit_app]
  refine congrArg
    (fun g ↦ (ν^*(X)[ModuleCat.{u + 1} Λ]).mapDerivedCategoryFactorsh.hom.app _ ≫ g) ?_
  erw [
    ← (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactorsh.inv.naturality,
    ← (Sheaf.restrictScalars (Scheme.ProEt.topology X) φ).mapDerivedCategoryFactorsh.inv.naturality]
  simp only [Functor.comp_map, ← DerivedCategory.Qh.map_comp_assoc, Category.assoc]
  rw [mapHomotopyCategory_unit_app_comp_map_comparisonUpperStarCompExtendScalarsIso]


variable (φ) in
/-- The base change map `Res(Rν_* N) ⟶ Rν_*(Res N)` of the restriction of scalars along `φ` with
`Rν_*`: the mate under the adjunctions `ν^* ⊣ Rν_*` of the commutation of `Res` with `ν^*`
(`derivedRestrictScalarsCompComparisonUpperStarIso`). -/
noncomputable def derivedRestrictScalarsCompComparisonLowerStarMap :
    R(ν_*(X)[ModuleCat.{u + 1} Λ']) ⋙ Sheaf.derivedRestrictScalars X.smallEtaleTopology φ ⟶
      Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ ⋙ R(ν_*(X)[ModuleCat.{u + 1} Λ]) :=
  mateEquiv (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ') X)
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X)
    (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom

/-- **The base change map of `Rν_*` for the derived extension of scalars, in restriction form**:
the transpose under `Ψ ⊣ Res` of `Rν_* L ⊗ᴸ_Λ Λ' ⟶ Rν_*(L ⊗ᴸ_Λ Λ')`
(`derivedExtendScalarsComparisonLowerStarMap`), followed by `Res Rν_* ⟶ Rν_* Res`
(`derivedRestrictScalarsCompComparisonLowerStarMap`), is `Rν_*` of the unit `L ⟶ Res(L ⊗ᴸ_Λ Λ')`.
-/
theorem unit_app_comp_map_derivedExtendScalarsComparisonLowerStarMap_app
    (L : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    (Etale.derivedExtendScalarsAdjunction hφ ha X).unit.app
        ((R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj L) ≫
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).map
        ((derivedExtendScalarsComparisonLowerStarMap hφ ha X).app L) ≫
      (derivedRestrictScalarsCompComparisonLowerStarMap φ X).app
        ((ProEtale.derivedExtendScalars hφ ha X).obj L) =
    (R(ν_*(X)[ModuleCat.{u + 1} Λ])).map
      ((ProEtale.derivedExtendScalarsAdjunction hφ ha X).unit.app L) := by
  apply ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have h₁ := mateEquiv_counit (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ') X)
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X)
    (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom
    ((ProEtale.derivedExtendScalars hφ ha X).obj L)
  have h₂ := (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom.naturality
    ((derivedExtendScalarsComparisonLowerStarMap hφ ha X).app L)
  have h₃ := mateEquiv_counit (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X)
    (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ') X)
    (TwoSquare.mk _ _ _ _ (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).inv) L
  have h₄ := unit_mateEquiv_symm (Etale.derivedExtendScalarsAdjunction hφ ha X)
    (ProEtale.derivedExtendScalarsAdjunction hφ ha X)
    (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom
    ((R(ν_*(X)[ModuleCat.{u + 1} Λ])).obj L)
  have h₅ : (mateEquiv (Etale.derivedExtendScalarsAdjunction hφ ha X)
      (ProEtale.derivedExtendScalarsAdjunction hφ ha X)).symm
        (derivedRestrictScalarsCompComparisonUpperStarIso φ X).hom =
      TwoSquare.mk _ _ _ _ (comparisonUpperStarDerivedExtendScalarsIso hφ ha X).hom :=
    (comparisonUpperStarDerivedExtendScalarsIso_hom_eq X hφ ha).symm
  rw [h₅] at h₄
  dsimp only [Functor.comp_map, Functor.comp_obj] at h₁ h₂ h₃ h₄
  erw [h₁, reassoc_of% h₂]
  rw [← Functor.map_comp]
  erw [h₃]
  rw [Functor.map_comp, reassoc_of% h₄, ← Functor.map_comp_assoc, Iso.hom_inv_id_app]
  erw [CategoryTheory.Functor.map_id, Category.id_comp]
  have hu := (ProEtale.derivedExtendScalarsAdjunction hφ ha X).unit.naturality
    ((derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).counit.app L)
  have hc := (derivedComparisonAdjunction (ModuleCat.{u + 1} Λ) X).counit.naturality
    ((ProEtale.derivedExtendScalarsAdjunction hφ ha X).unit.app L)
  dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hu hc
  rw [← hu, hc]

end AlgebraicGeometry.ProEtale
