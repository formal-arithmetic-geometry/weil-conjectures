/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.LeftProjectionMorphism
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedExtendScalarsIhomOfProjection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.LowerStarDualizable
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ExtendScalars.Projection
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Hom
public import WeilConjectures.SixFunctors.ProEtale.ScalarExtensionFlat

/-!
# Derived extension of scalars of pro-étale sheaves along a dualizable algebra commutes with
internal homs

Let `S` be an algebra over a commutative ring `R` such that the constant complex `S_X` of
`R`-modules is dualizable in `D(X_proét, R)`, for instance the reduction `R ⟶ R ⧸ (ϖⁿ)` modulo a
power of a nonzerodivisor. Write `Ψ = - ⊗ᴸ_R S : D(X_proét, R) ⥤ D(X_proét, S)` for the derived
extension of scalars, monoidal through `CategoryTheory.Functor.leftDerivedFunctorMonoidal`. Then
the comparison `Ψ RHom(K, L) ⟶ RHom(Ψ K, Ψ L)` is an isomorphism for all `K` and `L`.

Indeed, `Ψ` is left adjoint to the derived restriction of scalars `Res`, which reflects
isomorphisms, and satisfies the projection formula at the unit: the left projection morphism
`K ⊗ᴸ Res 𝟙 ⟶ Res (Ψ K ⊗ᴸ 𝟙)` is an isomorphism, being computed on K-flat complexes by the
projection map `K ⊗ S_X ⟶ Res (S ⊗_R K)` of sheaves
(`AlgebraicGeometry.ProEtale.sheafExtendScalarsProjection`). Since `Res 𝟙 = S_X` is dualizable,
the formal criterion
`CategoryTheory.Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_leftProjectionMorphism`
applies.

This is the pro-étale counterpart of `WeilConjectures.SixFunctors.Etale.Derived.ExtendScalarsHom`.

## Main results

- `AlgebraicGeometry.ProEtale.isIso_leftProjectionMorphism_leftDerivedSheafExtendScalars`:
  the projection formula `K ⊗ᴸ Res 𝟙 ≅ Res (Ψ K ⊗ᴸ 𝟙)` for derived extension of scalars.
- `AlgebraicGeometry.ProEtale.isIso_ihomComparison_leftDerivedSheafExtendScalars_of_isDualizable`:
  the comparison `Ψ RHom(K, L) ⟶ RHom(Ψ K, Ψ L)` is an isomorphism when `S_X` is dualizable.
- `AlgebraicGeometry.ProEtale.exists_isDerivedBaseChange_derivedHom_of_isDualizable`,
  `AlgebraicGeometry.ProEtale.exists_isDerivedBaseChange_derivedHom_quotient_span_pow`: in terms
  of derived base changes, `RHom(K', L')` is a derived base change of `RHom(K, L)` if `K'`, `L'`
  are derived base changes of `K`, `L`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Functor.LaxMonoidal Functor.OplaxMonoidal

open scoped CategoryTheory.Functor

attribute [local instance high] SymmetricCategory.toBraidedCategory
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory

-- `GrothendieckTopology.W.monoidal` gives the monoidality of `W` directly; the instance going
-- through enough points of the site is tried first and makes the search time out.
attribute [-instance] instIsMonoidalFunctorOppositeWOfHasSheafComposeForgetOfHasEnoughPoints

namespace AlgebraicGeometry.ProEtale

open Scheme

variable (R S : Type (u + 1)) [CommRing R] [CommRing S] [Algebra R S] (X : Scheme.{u})

/-- The unit of the derived adjunction `Ψ ⊣ Res` on the image of an object of the homotopy
category, followed by the counit of `Ψ` and the comparison for the exact restriction of scalars,
is the image of the unit of the adjunction induced on homotopy categories. -/
lemma leftDerivedSheafExtendScalarsAdjunction_unit_app_Qh_obj
    (K : HomotopyCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) (.up ℤ)) :
    (leftDerivedSheafExtendScalarsAdjunction R S X).unit.app (DerivedCategory.Qh.obj K) ≫
        (sheafCompose (ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapDerivedCategory.map
          ((sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorCounit.app K) ≫
        (sheafCompose (ProEt.topology X)
          (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).mapDerivedCategoryFactorsh.hom.app
          (((sheafExtendScalars (algebraMap R S) X).mapHomotopyCategory (.up ℤ)).obj K) =
      DerivedCategory.Qh.map
        (((sheafExtendScalarsAdjunction (algebraMap R S) X).mapHomotopyCategory
          (.up ℤ)).unit.app K) := by
  set r := sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))
  have h₁ := (sheafExtendScalarsAdjunction (algebraMap R S) X).mapHomotopyCategory (.up ℤ)
    |>.derivedη_fac_app (HomotopyCategory.quasiIso _ (.up ℤ))
    (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorCounit r.rightDerivedFunctorUnit K
  have h₃ := NatTrans.congr_app r.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
    (((sheafExtendScalars (algebraMap R S) X).mapHomotopyCategory (.up ℤ)).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at h₃
  have h₄ := r.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality
    ((sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorCounit.app K)
  simp only [leftDerivedSheafExtendScalarsAdjunction, Adjunction.derivedAdjunction,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  erw [← reassoc_of% h₄]
  erw [reassoc_of% h₁]
  rw [reassoc_of% h₃, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- The left projection morphism `B ⊗ Res 𝟙 ⟶ Res ((S ⊗_R B) ⊗ 𝟙)` of extension and restriction
of scalars of pro-étale sheaves, followed by the right unitor, is the projection map
`B ⊗ S_X ⟶ Res (S ⊗_R B)` of `AlgebraicGeometry.ProEtale.sheafExtendScalarsProjection`. -/
lemma sheafExtendScalarsAdjunction_leftProjectionMorphism_comp_map_rightUnitor
    (B : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    (sheafExtendScalarsAdjunction (algebraMap R S) X).leftProjectionMorphism B (𝟙_ _) ≫
      (sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map (ρ_ _).hom =
    (sheafExtendScalarsProjection R S X).app B := by
  rw [Adjunction.leftProjectionMorphism, ← Adjunction.homEquiv_naturality_right]
  dsimp only [sheafExtendScalarsProjection]
  rw [Adjunction.IsMonoidal.leftAdjoint_μ
    (adj := sheafExtendScalarsAdjunction (algebraMap R S) X)]
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

/-- **The projection formula for extension of scalars of pro-étale sheaves**, at the unit: the
left projection morphism `B ⊗ Res 𝟙 ⟶ Res ((S ⊗_R B) ⊗ 𝟙)` is an isomorphism. -/
lemma isIso_sheafExtendScalarsAdjunction_leftProjectionMorphism
    (B : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) :
    IsIso ((sheafExtendScalarsAdjunction (algebraMap R S) X).leftProjectionMorphism B (𝟙_ _)) := by
  have : IsIso ((sheafExtendScalarsAdjunction (algebraMap R S) X).leftProjectionMorphism B
      (𝟙_ _) ≫ (sheafCompose (ProEt.topology X)
        (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map (ρ_ _).hom) := by
    rw [sheafExtendScalarsAdjunction_leftProjectionMorphism_comp_map_rightUnitor]
    infer_instance
  exact IsIso.of_isIso_comp_right _
    ((sheafCompose (ProEt.topology X)
      (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))).map (ρ_ _).hom)

/-- The left projection morphisms of extension and restriction of scalars of pro-étale sheaves at
the components of the unit complex `𝟙 = S[0]` are isomorphisms. -/
lemma isIso_sheafExtendScalarsAdjunction_leftProjectionMorphism_tensorUnit_X
    (B : Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) (q : ℤ) :
    IsIso ((sheafExtendScalarsAdjunction (algebraMap R S) X).leftProjectionMorphism B
      ((𝟙_ (CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) ℤ)).X q)) := by
  by_cases hq : q = 0
  · subst hq
    exact (Adjunction.isIso_leftProjectionMorphism_iff_of_iso_right _ B
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (𝟙_ (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S))))).2
      (isIso_sheafExtendScalarsAdjunction_leftProjectionMorphism R S X B)
  · have hZ : IsZero
        ((𝟙_ (CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S)) ℤ)).X q) :=
      HomologicalComplex.isZero_single_obj_X _ _ _ _ hq
    let r := sheafCompose (ProEt.topology X) (ModuleCat.restrictScalars.{u + 1} (algebraMap R S))
    exact isIso_of_source_target_iso_zero _
      (MonoidalCategory.isZero_tensorObj_of_isZero_right B (r.map_isZero hZ)).isoZero
      (r.map_isZero (MonoidalCategory.isZero_tensorObj_of_isZero_right _ hZ)).isoZero

/-- **The projection formula for derived extension of scalars of pro-étale sheaves**, at the
unit: for the derived extension of scalars `Ψ`, monoidal through
`CategoryTheory.Functor.leftDerivedFunctorMonoidal`, the left projection morphism
`K ⊗ᴸ Res 𝟙 ⟶ Res (Ψ K ⊗ᴸ 𝟙)` of `Ψ ⊣ Res` is an isomorphism. -/
theorem isIso_leftProjectionMorphism_leftDerivedSheafExtendScalars
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))) :
    letI := (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorMonoidal
    IsIso ((leftDerivedSheafExtendScalarsAdjunction R S X).leftProjectionMorphism K (𝟙_ _)) := by
  let := (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorMonoidal
  have := DerivedCategory.isIso_ε_Qh (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S))
  rw [← Adjunction.isIso_leftProjectionMorphism_iff_of_iso_right _ K
    (asIso (ε (DerivedCategory.Qh (C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S))))).symm]
  exact Adjunction.isIso_derivedLeftProjectionMorphism_Qh_obj
    (sheafExtendScalarsAdjunction (algebraMap R S) X)
    (leftDerivedSheafExtendScalarsAdjunction R S X)
    (leftDerivedSheafExtendScalarsAdjunction_counit_app_Qh_obj R S X)
    (leftDerivedSheafExtendScalarsAdjunction_unit_app_Qh_obj R S X) _
    (isIso_sheafExtendScalarsAdjunction_leftProjectionMorphism_tensorUnit_X R S X) K

/-- The derived restriction of scalars of the unit `𝟙 = S[0]` of `D(X_proét, S)` is the constant
complex `S_X` of `R`-modules placed in degree `0`. -/
noncomputable def derivedRestrictScalarsTensorUnitIso :
    (Sheaf.derivedRestrictScalars (ProEt.topology X) (algebraMap R S)).obj (𝟙_ _) ≅
      (DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) 0).obj
        ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj
          ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj
            (𝟙_ (ModuleCat.{u + 1} S)))) :=
  have := DerivedCategory.isIso_ε_Qh (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S))
  (Sheaf.derivedRestrictScalars (ProEt.topology X) (algebraMap R S)).mapIso
      (asIso (ε (DerivedCategory.Qh (C := Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S))))) ≪≫
    (Sheaf.restrictScalars (ProEt.topology X) (algebraMap R S)).mapDerivedCategoryFactorsh.app _ ≪≫
    DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ _).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex
        (Sheaf.restrictScalars (ProEt.topology X) (algebraMap R S)) (ComplexShape.up ℤ) 0).app
          (𝟙_ _))) ≪≫
    derivedSingleSheafRestrictScalarsUnitIso R S X

/-- **Derived extension of scalars of pro-étale sheaves along a dualizable algebra commutes with
internal homs.** For an `R`-algebra `S` such that the constant complex `S_X` of `R`-modules is
dualizable, the comparison `Ψ RHom(K, L) ⟶ RHom(Ψ K, Ψ L)` of the derived extension of scalars
`Ψ = - ⊗ᴸ_R S`, monoidal through `CategoryTheory.Functor.leftDerivedFunctorMonoidal`, is an
isomorphism. -/
theorem isIso_ihomComparison_leftDerivedSheafExtendScalars_of_isDualizable
    (hS : IsDualizable
      ((DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) 0).obj
        ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj
          ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj
            (𝟙_ (ModuleCat.{u + 1} S))))))
    (K L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))) :
    letI := (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorMonoidal
    IsIso ((ihomComparison L(sheafExtendScalars (algebraMap R S) X) K).app L) := by
  let := (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorMonoidal
  obtain ⟨_⟩ := hS.of_iso (derivedRestrictScalarsTensorUnitIso R S X).symm
  obtain ⟨_⟩ := DerivedCategory.nonempty_braidedCategory
    (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))
  let := BraidedCategory.exactPairing_swap
    ((Sheaf.derivedRestrictScalars (ProEt.topology X) (algebraMap R S)).obj (𝟙_ _))
    ((Sheaf.derivedRestrictScalars (ProEt.topology X) (algebraMap R S)).obj (𝟙_ _))ᘁ
  exact Functor.LaxMonoidal.isIso_ihomComparison_of_isIso_leftProjectionMorphism _
    (leftDerivedSheafExtendScalarsAdjunction R S X)
    ((Sheaf.derivedRestrictScalars (ProEt.topology X) (algebraMap R S)).obj (𝟙_ _))ᘁ
    (isIso_leftProjectionMorphism_leftDerivedSheafExtendScalars R S X) K L

/-- The unit `K ⟶ Res (Ψ K)` of derived extension of scalars of pro-étale sheaves exhibits
`Ψ K = K ⊗ᴸ_R S` as a derived base change of `K`. -/
lemma isDerivedBaseChange_leftDerivedSheafExtendScalarsAdjunction_unit
    (K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))) :
    Sheaf.IsDerivedBaseChange (f := algebraMap R S)
      ((leftDerivedSheafExtendScalarsAdjunction R S X).unit.app K) := fun N ↦ by
  convert ((leftDerivedSheafExtendScalarsAdjunction R S X).homEquiv K N).bijective using 1
  ext g
  exact ((leftDerivedSheafExtendScalarsAdjunction R S X).homEquiv_unit K N g).symm

/-- Any derived base change `K'` of `K` along `R → S` is isomorphic to `Ψ K = K ⊗ᴸ_R S`. -/
lemma nonempty_iso_leftDerivedSheafExtendScalars_of_isDerivedBaseChange
    {K : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))}
    {K' : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars (ProEt.topology X) (algebraMap R S)).obj K'}
    (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty ((L(sheafExtendScalars (algebraMap R S) X)).obj K ≅ K') := by
  let adj := leftDerivedSheafExtendScalarsAdjunction R S X
  have := Sheaf.IsDerivedBaseChange.isIso
    (isDerivedBaseChange_leftDerivedSheafExtendScalarsAdjunction_unit R S X K) hη
    ((adj.homEquiv K K').symm η)
    ((adj.homEquiv_unit K K' _).symm.trans (Equiv.apply_symm_apply _ η))
  exact ⟨asIso ((adj.homEquiv K K').symm η)⟩

/-- **The internal hom of pro-étale sheaves commutes with derived base change along a
dualizable algebra**: if the constant complex `S_X` of `R`-modules is dualizable and `K'`, `L'`
are derived base changes of `K`, `L` along `R → S`, then `RHom_S(K', L')` is a derived base
change of `RHom_R(K, L)`. -/
theorem exists_isDerivedBaseChange_derivedHom_of_isDualizable
    (hS : IsDualizable
      ((DerivedCategory.singleFunctor (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) 0).obj
        ((constantSheaf (ProEt.topology X) (ModuleCat.{u + 1} R)).obj
          ((ModuleCat.restrictScalars.{u + 1} (algebraMap R S)).obj
            (𝟙_ (ModuleCat.{u + 1} S))))))
    {K L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R))}
    {K' L' : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} S))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars (ProEt.topology X) (algebraMap R S)).obj K'}
    {η' : L ⟶ (Sheaf.derivedRestrictScalars (ProEt.topology X) (algebraMap R S)).obj L'}
    (hη : Sheaf.IsDerivedBaseChange η) (hη' : Sheaf.IsDerivedBaseChange η') :
    ∃ θ : ((derivedHom (ModuleCat.{u + 1} R) X).obj (op K)).obj L ⟶
        (Sheaf.derivedRestrictScalars (ProEt.topology X) (algebraMap R S)).obj
          (((derivedHom (ModuleCat.{u + 1} S) X).obj (op K')).obj L'),
      Sheaf.IsDerivedBaseChange θ := by
  let := (sheafExtendScalars (algebraMap R S) X).leftDerivedFunctorMonoidal
  obtain ⟨eK⟩ := nonempty_iso_leftDerivedSheafExtendScalars_of_isDerivedBaseChange R S X hη
  obtain ⟨eL⟩ := nonempty_iso_leftDerivedSheafExtendScalars_of_isDerivedBaseChange R S X hη'
  have := isIso_ihomComparison_leftDerivedSheafExtendScalars_of_isDualizable R S X hS K L
  exact ⟨_, (isDerivedBaseChange_leftDerivedSheafExtendScalarsAdjunction_unit R S X _)
    |>.comp_map_iso
    (asIso ((ihomComparison L(sheafExtendScalars (algebraMap R S) X) K).app L) ≪≫
      ((derivedHom (ModuleCat.{u + 1} S) X).mapIso eK.symm.op).app _ ≪≫
      ((derivedHom (ModuleCat.{u + 1} S) X).obj (op K')).mapIso eL)⟩

/-- **Reduction modulo a power of a nonzerodivisor commutes with internal homs of pro-étale
sheaves**: for a nonzerodivisor `ϖ` of `Λ` and `n : ℕ`, if `Kn`, `Ln` are derived base changes
of `K`, `L` along `Λ ⟶ Λ ⧸ (ϖ)ⁿ`, then `RHom(Kn, Ln)` is a derived base change of
`RHom(K, L)`. -/
theorem exists_isDerivedBaseChange_derivedHom_quotient_span_pow {Λ : Type (u + 1)} [CommRing Λ]
    (X : Scheme.{u}) {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ)
    {K L : DerivedCategory (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} Λ))}
    {Kn Ln : DerivedCategory (Sheaf (ProEt.topology X)
      (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)))}
    {η : K ⟶ (Sheaf.derivedRestrictScalars (ProEt.topology X)
      (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n))).obj Kn}
    {η' : L ⟶ (Sheaf.derivedRestrictScalars (ProEt.topology X)
      (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n))).obj Ln}
    (hη : Sheaf.IsDerivedBaseChange η) (hη' : Sheaf.IsDerivedBaseChange η') :
    ∃ θ : ((derivedHom (ModuleCat.{u + 1} Λ) X).obj (op K)).obj L ⟶
        (Sheaf.derivedRestrictScalars (ProEt.topology X)
          (Ideal.Quotient.mk (Ideal.span {ϖ} ^ n))).obj
          (((derivedHom (ModuleCat.{u + 1} (Λ ⧸ Ideal.span {ϖ} ^ n)) X).obj (op Kn)).obj Ln),
      Sheaf.IsDerivedBaseChange θ :=
  exists_isDerivedBaseChange_derivedHom_of_isDualizable Λ (Λ ⧸ Ideal.span {ϖ} ^ n) X
    ((isDualizable_singleFunctor_constantSheaf_quotient_span_pow hϖ n X).of_iso
      ((DerivedCategory.singleFunctor _ 0).mapIso ((constantSheaf _ _).mapIso
        (restrictScalarsAlgebraMapUnitIso _ _).symm))) hη hη'

end AlgebraicGeometry.ProEtale
