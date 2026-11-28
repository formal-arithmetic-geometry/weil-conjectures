/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ReductionExtendScalars
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.LeftProjectionMorphism
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsIhomOfProjection
public import WeilConjectures.SixFunctors.Etale.Derived.CoefficientChangeLowerStarFiniteType
public import WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Hom
public import WeilConjectures.SixFunctors.Etale.ScalarExtension.ProjectionIso

/-!
# Derived extension of scalars along a dualizable algebra commutes with internal homs

Let `φ : Λ →+* Λ'` be a morphism of commutative rings such that the constant complex `Λ'_X` of
`Λ`-modules is dualizable in `D(X_ét, Λ)`, for instance the reduction `Λ ⟶ Λ ⧸ (ϖⁿ)` modulo a
power of a nonzerodivisor. Write `Ψ = - ⊗ᴸ_Λ Λ' : D(X_ét, Λ) ⥤ D(X_ét, Λ')` for the derived
extension of scalars, monoidal through `CategoryTheory.Functor.leftDerivedFunctorMonoidal`. Then
the comparison `Ψ RHom(K, L) ⟶ RHom(Ψ K, Ψ L)` is an isomorphism for all `K` and `L`.

Indeed, `Ψ` is left adjoint to the derived restriction of scalars `Res`, which reflects
isomorphisms, and satisfies the projection formula at the unit: the left projection morphism
`K ⊗ᴸ Res 𝟙 ⟶ Res (Ψ K ⊗ᴸ 𝟙)` is an isomorphism, being computed on K-flat complexes by the
projection map `K ⊗ Λ'_X ⟶ Res (Λ' ⊗_Λ K)` of sheaves
(`AlgebraicGeometry.Etale.sheafExtendScalarsProjection`). Since `Res 𝟙 = Λ'_X` is dualizable, the
formal criterion
`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_leftProjectionMorphism`
applies.

## Main results

- `AlgebraicGeometry.Etale.isIso_leftProjectionMorphism_leftDerivedEtaleSheafExtendScalars`:
  the projection formula `K ⊗ᴸ Res 𝟙 ≅ Res (Ψ K ⊗ᴸ 𝟙)` for derived extension of scalars.
- `AlgebraicGeometry.Etale.isIso_ihomComparison_leftDerivedSheafExtendScalars_of_isDualizable`:
  the comparison `Ψ RHom(K, L) ⟶ RHom(Ψ K, Ψ L)` is an isomorphism when `Λ'_X` is dualizable.
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedSheafExtendScalars_derivedHom_of_isDualizable`:
  the resulting isomorphism `Ψ RHom(K, L) ≅ RHom(Ψ K, Ψ L)`.
- `AlgebraicGeometry.Etale.nonempty_iso_leftDerivedSheafExtendScalars_derivedHom_quotient_span_pow`:
  the case of the reduction `Λ ⟶ Λ ⧸ (ϖ)ⁿ` modulo a power of a nonzerodivisor.
- `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_derivedHom_of_isDualizable`,
  `AlgebraicGeometry.Etale.exists_isDerivedBaseChange_derivedHom_quotient_span_pow`: the same
  statements in terms of derived base changes: `RHom(K', L')` is a derived base change of
  `RHom(K, L)` if `K'`, `L'` are derived base changes of `K`, `L`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

-- Use the monoidal structure of the derived tensor product of étale sheaves, see
-- `WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsDerived`.
attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.Etale.sheafBraidedCategory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (φ : Λ →+* Λ') (X : Scheme.{u})

/-- The unit of the derived adjunction `Ψ ⊣ Res` on the image of an object `K` of the homotopy
category, followed by the counit of `Ψ` and the comparison for the exact restriction of scalars,
is the image of the unit of the adjunction induced on homotopy categories. -/
lemma leftDerivedEtaleSheafExtendScalarsAdjunction_unit_app_Qh_obj
    (K : HomotopyCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (.up ℤ)) :
    (leftDerivedEtaleSheafExtendScalarsAdjunction φ X).unit.app (DerivedCategory.Qh.obj K) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategory.map
          ((sheafExtendScalars φ X).leftDerivedFunctorCounit.app K) ≫
        (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryFactorsh.hom.app
          (((sheafExtendScalars φ X).mapHomotopyCategory (.up ℤ)).obj K) =
      DerivedCategory.Qh.map
        (((sheafExtendScalarsAdjunction φ X).mapHomotopyCategory (.up ℤ)).unit.app K) := by
  set r := Sheaf.restrictScalars X.smallEtaleTopology φ
  have h₁ := (sheafExtendScalarsAdjunction φ X).mapHomotopyCategory (.up ℤ)
    |>.derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
    (sheafExtendScalars φ X).leftDerivedFunctorCounit r.rightDerivedFunctorUnit K
  have h₃ := NatTrans.congr_app r.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    (((sheafExtendScalars φ X).mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  have h₄ := r.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    ((sheafExtendScalars φ X).leftDerivedFunctorCounit.app K)
  simp only [leftDerivedEtaleSheafExtendScalarsAdjunction, Adjunction.derivedAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  erw [← reassoc_of% h₄]
  erw [reassoc_of% h₁]
  rw [reassoc_of% h₃, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- The left projection morphism `B ⊗ Res 𝟙 ⟶ Res ((Λ' ⊗_Λ B) ⊗ 𝟙)` of extension and restriction
of scalars of étale sheaves, followed by the right unitor, is the projection map
`B ⊗ Λ'_X ⟶ Res (Λ' ⊗_Λ B)` of `AlgebraicGeometry.Etale.sheafExtendScalarsProjection`. -/
lemma sheafExtendScalarsAdjunction_leftProjectionMorphism_comp_map_rightUnitor
    [Algebra Λ Λ'] (B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (sheafExtendScalarsAdjunction (algebraMap Λ Λ') X).leftProjectionMorphism B (𝟙_ _) ≫
      (sheafCompose X.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1} (algebraMap Λ Λ'))).map (ρ_ _).hom =
    (sheafExtendScalarsProjection Λ Λ' X).app B := by
  rw [Adjunction.leftProjectionMorphism, ← Adjunction.homEquiv_naturality_right]
  dsimp only [sheafExtendScalarsProjection]
  rw [Adjunction.IsMonoidal.leftAdjoint_μ (adj := sheafExtendScalarsAdjunction (algebraMap Λ Λ') X)]
  simp only [Category.assoc]
  erw [← Adjunction.unit_naturality_assoc]
  rw [← Functor.map_comp, ← Functor.map_comp, Adjunction.homEquiv_unit]
  congr 2
  simp only [Category.assoc]
  erw [← δ_natural_left_assoc]
  erw [MonoidalCategory.tensorHom_def]
  simp only [Category.assoc]
  erw [← comp_whiskerRight_assoc, Adjunction.left_triangle_components, id_whiskerRight,
    Category.id_comp]
  rfl

/-- **The projection formula for extension of scalars of étale sheaves**, at the unit: the left
projection morphism `B ⊗ Res 𝟙 ⟶ Res ((Λ' ⊗_Λ B) ⊗ 𝟙)` is an isomorphism. -/
lemma isIso_sheafExtendScalarsAdjunction_leftProjectionMorphism
    (B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    IsIso ((sheafExtendScalarsAdjunction φ X).leftProjectionMorphism B (𝟙_ _)) := by
  let := φ.toAlgebra
  have h := sheafExtendScalarsAdjunction_leftProjectionMorphism_comp_map_rightUnitor (Λ' := Λ') X B
  have : IsIso ((sheafExtendScalarsAdjunction (algebraMap Λ Λ') X).leftProjectionMorphism B
      (𝟙_ _) ≫ (sheafCompose X.smallEtaleTopology
        (ModuleCat.restrictScalars.{u + 1} (algebraMap Λ Λ'))).map (ρ_ _).hom) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ)).map (ρ_ _).hom)

/-- The left projection morphisms of extension and restriction of scalars of étale sheaves at the
components of the unit complex `𝟙 = Λ'[0]` are isomorphisms. -/
lemma isIso_sheafExtendScalarsAdjunction_leftProjectionMorphism_tensorUnit_X
    (B : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) :
    IsIso ((sheafExtendScalarsAdjunction φ X).leftProjectionMorphism B
      ((𝟙_ (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) ℤ)).X q)) := by
  by_cases hq : q = 0
  · subst hq
    exact (Adjunction.isIso_leftProjectionMorphism_iff_of_iso_right _ B
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))))).2
      (isIso_sheafExtendScalarsAdjunction_leftProjectionMorphism φ X B)
  · have hZ : IsZero
        ((𝟙_ (CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ')) ℤ)).X q) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ hq
    let R := sheafCompose X.smallEtaleTopology (ModuleCat.restrictScalars.{u + 1} φ)
    exact isIso_of_source_target_iso_zero _
      (MonoidalCategory.isZero_tensorObj_of_isZero_right B (R.map_isZero hZ)).isoZero
      (R.map_isZero (MonoidalCategory.isZero_tensorObj_of_isZero_right _ hZ)).isoZero

/-- Extension of scalars of étale sheaves preserves flat objects. -/
instance preservesFlat_sheafExtendScalars : (sheafExtendScalars φ X).PreservesFlat :=
  Sheaf.preservesFlat_extendScalars X.smallEtaleTopology (f := φ)

/-- **The projection formula for derived extension of scalars**, at the unit: for the derived
extension of scalars `Ψ`, monoidal through `CategoryTheory.Functor.leftDerivedFunctorMonoidal`,
the left projection morphism `K ⊗ᴸ Res 𝟙 ⟶ Res (Ψ K ⊗ᴸ 𝟙)` of `Ψ ⊣ Res` is an isomorphism. -/
theorem isIso_leftProjectionMorphism_leftDerivedEtaleSheafExtendScalars
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := (sheafExtendScalars φ X).leftDerivedFunctorMonoidal
    IsIso ((leftDerivedEtaleSheafExtendScalarsAdjunction φ X).leftProjectionMorphism K
      (𝟙_ _)) := by
  let := (sheafExtendScalars φ X).leftDerivedFunctorMonoidal
  have := DerivedCategory.isIso_ε_Qh (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
  rw [← Adjunction.isIso_leftProjectionMorphism_iff_of_iso_right _ K
    (asIso (ε (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))))).symm]
  exact Adjunction.isIso_derivedLeftProjectionMorphism_Qh_obj (sheafExtendScalarsAdjunction φ X)
    (leftDerivedEtaleSheafExtendScalarsAdjunction φ X)
    (leftDerivedEtaleSheafExtendScalarsAdjunction_counit_app_Qh_obj φ X)
    (leftDerivedEtaleSheafExtendScalarsAdjunction_unit_app_Qh_obj φ X) _
    (isIso_sheafExtendScalarsAdjunction_leftProjectionMorphism_tensorUnit_X φ X) K

/-- The derived restriction of scalars of the unit `𝟙 = Λ'[0]` of `D(X_ét, Λ')` is the constant
complex `Λ'_X` of `Λ`-modules placed in degree `0`. -/
noncomputable def derivedRestrictScalarsTensorUnitIso :
    (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj (𝟙_ _) ≅
      constantSingle (ModuleCat.{u + 1} Λ) X
        ((ModuleCat.restrictScalars.{u + 1} φ).obj (𝟙_ (ModuleCat.{u + 1} Λ'))) :=
  let := φ.toAlgebra
  have := DerivedCategory.isIso_ε_Qh (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))
  (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).mapIso
      (asIso (ε (DerivedCategory.Qh (C := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))))) ≪≫
    (Sheaf.restrictScalars X.smallEtaleTopology φ).mapDerivedCategoryFactorsh.app _ ≪≫
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ _).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Sheaf.restrictScalars X.smallEtaleTopology φ) (ComplexShape.up ℤ) 0).app (𝟙_ _))) ≪≫
    derivedSingleSheafRestrictScalarsUnitIso Λ Λ' X

/-- **Derived extension of scalars along a dualizable algebra commutes with internal homs.** For
a ring homomorphism `φ : Λ →+* Λ'` such that the constant complex `Λ'_X` of `Λ`-modules is
dualizable, the comparison `Ψ RHom(K, L) ⟶ RHom(Ψ K, Ψ L)` of the derived extension of scalars
`Ψ = - ⊗ᴸ_Λ Λ'`, monoidal through `CategoryTheory.Functor.leftDerivedFunctorMonoidal`, is an
isomorphism. -/
theorem isIso_ihomComparison_leftDerivedSheafExtendScalars_of_isDualizable
    (hΛ' : IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) X
      ((ModuleCat.restrictScalars.{u + 1} φ).obj (𝟙_ (ModuleCat.{u + 1} Λ')))))
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    letI := (sheafExtendScalars φ X).leftDerivedFunctorMonoidal
    IsIso ((ihomComparison L(sheafExtendScalars φ X) K).app L) := by
  let := (sheafExtendScalars φ X).leftDerivedFunctorMonoidal
  obtain ⟨_⟩ := hΛ'.of_iso (derivedRestrictScalarsTensorUnitIso φ X).symm
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory
    (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  let := BraidedCategory.exactPairing_swap
    ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj (𝟙_ _))
    ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj (𝟙_ _))ᘁ
  exact Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_leftProjectionMorphism _
    (leftDerivedEtaleSheafExtendScalarsAdjunction φ X)
    ((Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj (𝟙_ _))ᘁ
    (isIso_leftProjectionMorphism_leftDerivedEtaleSheafExtendScalars φ X) K L

/-- **Derived extension of scalars along a dualizable algebra commutes with internal homs**: for
a ring homomorphism `φ : Λ →+* Λ'` such that the constant complex `Λ'_X` of `Λ`-modules is
dualizable, `RHom(K, L) ⊗ᴸ_Λ Λ' ≅ RHom(K ⊗ᴸ_Λ Λ', L ⊗ᴸ_Λ Λ')` for all `K`, `L` in
`D(X_ét, Λ)`. -/
theorem nonempty_iso_leftDerivedSheafExtendScalars_derivedHom_of_isDualizable
    (hΛ' : IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) X
      ((ModuleCat.restrictScalars.{u + 1} φ).obj (𝟙_ (ModuleCat.{u + 1} Λ')))))
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((L(sheafExtendScalars φ X)).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L) ≅
      ((derivedHom (ModuleCat.{u + 1} Λ') X).obj (op ((L(sheafExtendScalars φ X)).obj K))).obj
        ((L(sheafExtendScalars φ X)).obj L)) :=
  let := (sheafExtendScalars φ X).leftDerivedFunctorMonoidal
  have := isIso_ihomComparison_leftDerivedSheafExtendScalars_of_isDualizable φ X hΛ' K L
  ⟨asIso ((ihomComparison L(sheafExtendScalars φ X) K).app L)⟩

/-- Any derived base change `K'` of `K` along `φ` is isomorphic to `Ψ K = K ⊗ᴸ_Λ Λ'`. -/
lemma nonempty_iso_leftDerivedSheafExtendScalars_of_isDerivedBaseChange
    {K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty ((L(sheafExtendScalars φ X)).obj K ≅ K') := by
  let adj := leftDerivedEtaleSheafExtendScalarsAdjunction φ X
  have := Sheaf.IsDerivedBaseChange.isIso
    (isDerivedBaseChange_leftDerivedEtaleSheafExtendScalarsAdjunction_unit φ X K) hη
    ((adj.homEquiv K K').symm η)
    ((adj.homEquiv_unit K K' _).symm.trans (Equiv.apply_symm_apply _ η))
  exact ⟨asIso ((adj.homEquiv K K').symm η)⟩

/-- **The internal hom commutes with derived base change along a dualizable algebra**: if the
constant complex `Λ'_X` of `Λ`-modules is dualizable and `K'`, `L'` are derived base changes of
`K`, `L` along `φ`, then `RHom_{Λ'}(K', L')` is a derived base change of `RHom_Λ(K, L)`. -/
theorem exists_isDerivedBaseChange_derivedHom_of_isDualizable
    (hΛ' : IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) X
      ((ModuleCat.restrictScalars.{u + 1} φ).obj (𝟙_ (ModuleCat.{u + 1} Λ')))))
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' L' : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ'))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj K'}
    {η' : L ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj L'}
    (hη : Sheaf.IsDerivedBaseChange η) (hη' : Sheaf.IsDerivedBaseChange η') :
    ∃ θ : ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L ⟶
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ).obj
          (((derivedHom (ModuleCat.{u + 1} Λ') X).obj (op K')).obj L'),
      Sheaf.IsDerivedBaseChange θ := by
  obtain ⟨eK⟩ := nonempty_iso_leftDerivedSheafExtendScalars_of_isDerivedBaseChange φ X hη
  obtain ⟨eL⟩ := nonempty_iso_leftDerivedSheafExtendScalars_of_isDerivedBaseChange φ X hη'
  obtain ⟨e⟩ := nonempty_iso_leftDerivedSheafExtendScalars_derivedHom_of_isDualizable φ X hΛ' K L
  exact ⟨_, (isDerivedBaseChange_leftDerivedEtaleSheafExtendScalarsAdjunction_unit φ X _)
    |>.comp_map_iso
    (e ≪≫ ((derivedHom (ModuleCat.{u + 1} Λ') X).mapIso eK.symm.op).app _ ≪≫
      ((derivedHom (ModuleCat.{u + 1} Λ') X).obj (op K')).mapIso eL)⟩

section QuotientSpanPow

/-- For a nonzerodivisor `ϖ` of `Λ` and `n : ℕ`, the constant complex `(Λ ⧸ (ϖ)ⁿ)_X` of
`Λ`-modules underlying the unit of `Λ ⧸ (ϖ)ⁿ`-modules is dualizable. -/
lemma isDualizable_constantSingle_restrictScalars_quotient_span_pow {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) :
    IsDualizable (constantSingle (ModuleCat.{u + 1} Λ) X
      ((ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n))).obj
        (𝟙_ (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n))))) :=
  (isDualizable_constantSingle_quotient_span_pow hϖ n X).of_iso
    ((DerivedCategory.singleFunctor _ 0).mapIso ((constantSheaf _ _).mapIso
      (LinearEquiv.toModuleIso (X₁ := Λ ⧸ Ideal.span {ϖ} ^ n)
        (X₂ := (ModuleCat.restrictScalars.{u + 1} (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n))).obj
          (𝟙_ (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n))))
        { toFun := id
          invFun := id
          map_add' _ _ := rfl
          map_smul' _ _ := rfl
          left_inv _ := rfl
          right_inv _ := rfl })))

/-- **Reduction modulo a power of a nonzerodivisor commutes with internal homs**: for a
nonzerodivisor `ϖ` of `Λ` and `n : ℕ`, writing `Ψ = - ⊗ᴸ_Λ Λ ⧸ (ϖ)ⁿ`, there is an isomorphism
`Ψ RHom(K, L) ≅ RHom(Ψ K, Ψ L)` for all `K`, `L` in `D(X_ét, Λ)`. -/
theorem nonempty_iso_leftDerivedSheafExtendScalars_derivedHom_quotient_span_pow {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ)
    (K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Nonempty ((L(sheafExtendScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) X)).obj
        (((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L) ≅
      ((derivedHom (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)) X).obj
          (op ((L(sheafExtendScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) X)).obj K))).obj
        ((L(sheafExtendScalars (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n)) X)).obj L)) :=
  nonempty_iso_leftDerivedSheafExtendScalars_derivedHom_of_isDualizable _ X
    (isDualizable_constantSingle_restrictScalars_quotient_span_pow X hϖ n) K L

/-- **Reduction modulo a power of a nonzerodivisor commutes with internal homs**, in terms of
derived base changes: if `K'`, `L'` are derived base changes of `K`, `L` along
`Λ ⟶ Λ ⧸ (ϖ)ⁿ`, then `RHom(K', L')` is a derived base change of `RHom(K, L)`. -/
theorem exists_isDerivedBaseChange_derivedHom_quotient_span_pow {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ)
    {K L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    {K' L' : DerivedCategory (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n))).obj K'}
    {η' : L ⟶ (Sheaf.derivedRestrictScalars X.smallEtaleTopology
      (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n))).obj L'}
    (hη : Sheaf.IsDerivedBaseChange η) (hη' : Sheaf.IsDerivedBaseChange η') :
    ∃ θ : ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L ⟶
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology
          (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n))).obj
          (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)) X).obj (op K')).obj L'),
      Sheaf.IsDerivedBaseChange θ :=
  exists_isDerivedBaseChange_derivedHom_of_isDualizable _ X
    (isDualizable_constantSingle_restrictScalars_quotient_span_pow X hϖ n) hη hη'

end QuotientSpanPow

end AlgebraicGeometry.Etale
