/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence

/-!
# The Kummer classes under a change of coefficients

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings whose characteristics satisfy
`n = n' e` (for instance the reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ`, with `e = ℓ`). The Kummer
sequences of `n` and `n'` are related by the `e`-th power maps
(`AlgebraicGeometry.Scheme.kummerSequencePowMap`), and extension of scalars along `ρ` gives a
morphism `Λ ⊗ F ⟶ Λ' ⊗ F` of sheaves of `Λ`-modules
(`AlgebraicGeometry.Etale.extendScalarsChangeMap`). Together they give a morphism from the
pulled back Kummer sequence with coefficients `Λ` to the one with coefficients `Λ'`, with scalars
restricted to `Λ`, so that the connecting morphisms correspond
(`AlgebraicGeometry.Etale.kummerδ_comp_changeMap`): the change of coefficients of the Kummer
class of a unit is its Kummer class.
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace CategoryTheory.ShortComplex

variable {C : Type*} [Category* C] [Abelian C] {S S' : ShortComplex C} (σ : S ⟶ S') {Y : C}
  (φ : Y ⟶ S.X₃)
  (φ' : Y ⟶ S'.X₃) (h : φ ≫ σ.τ₃ = φ')

/-- A morphism of short complexes `σ : S ⟶ S'` induces a morphism from the pullback of `S`
along `φ : Y ⟶ S.X₃` to the pullback of `S'` along `φ' = φ ≫ σ.τ₃`, which is the identity on
`Y`. -/
@[simps]
noncomputable def pullbackMapOfHom : S.pullback φ ⟶ S'.pullback φ' where
  τ₁ := σ.τ₁
  τ₂ := Limits.pullback.map _ _ _ _ σ.τ₂ (𝟙 Y) σ.τ₃ σ.comm₂₃.symm (by simp [h])
  τ₃ := 𝟙 Y
  comm₁₂ := by
    apply Limits.pullback.hom_ext
    · simp only [ShortComplex.pullback, Limits.pullback.map, Category.assoc,
        Limits.pullback.lift_fst, Limits.pullback.lift_fst_assoc]
      exact σ.comm₁₂
    · simp only [ShortComplex.pullback, Limits.pullback.map, Category.assoc,
        Limits.pullback.lift_snd, Limits.pullback.lift_snd_assoc, comp_zero, zero_comp]
  comm₂₃ := by
    simp only [ShortComplex.pullback, Limits.pullback.map, Limits.pullback.lift_snd,
      Category.comp_id]

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry

namespace Scheme

variable {X : Scheme.{u}}

/-- The morphism of Kummer sequences `0 ⟶ μ_c ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` to
`0 ⟶ μ_a ⟶ 𝔾ₘ ⟶ 𝔾ₘ ⟶ 0` given by the `b`-th power maps on `μ_c` and on the middle `𝔾ₘ`, and
the identity on the last `𝔾ₘ`, for `c = a b`. -/
@[simps]
noncomputable def kummerSequencePowMap (a b c : ℕ) (h : c = a * b) :
    X.kummerSequence c ⟶ X.kummerSequence a where
  τ₁ := rootsOfUnityPow a b c h
  τ₂ := b • 𝟙 X.gmSheaf
  τ₃ := 𝟙 X.gmSheaf
  comm₁₂ := rootsOfUnityPow_ι a b c h
  comm₂₃ := by
    change (b • 𝟙 X.gmSheaf) ≫ (a • 𝟙 X.gmSheaf) = (c • 𝟙 X.gmSheaf) ≫ 𝟙 _
    rw [Category.comp_id, nsmul_id_comp_nsmul_id, h]

end Scheme

namespace Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})

/-- The change of coefficients `Λ ⊗ F ⟶ Λ' ⊗ F` along `ρ : Λ →+* Λ'` of the extension of
scalars of an étale sheaf of abelian groups `F`, as a morphism of sheaves of `Λ`-modules: the
adjoint of the unit `F ⟶ Λ' ⊗ F`. -/
noncomputable def extendScalarsChangeMap :
    extendScalars Λ X ⟶ extendScalars Λ' X ⋙ Sheaf.restrictScalars X.smallEtaleTopology ρ where
  app F := (extendScalars Λ X).map ((extendScalarsAdjunction Λ' X).unit.app F) ≫
    (extendScalarsAdjunction Λ X).counit.app ((Sheaf.restrictScalars X.smallEtaleTopology ρ).obj
      ((extendScalars Λ' X).obj F))
  naturality F G g := by
    have h := (extendScalarsAdjunction Λ' X).unit.naturality g
    have h' := (extendScalarsAdjunction Λ X).counit.naturality
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).map ((extendScalars Λ' X).map g))
    dsimp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at h h' ⊢
    refine (Functor.map_comp_assoc _ _ _ _).symm.trans ?_
    erw [h]
    refine (Functor.map_comp_assoc _ _ _ _).trans ?_
    erw [h']
    exact (Category.assoc _ _ _).symm

end Etale

end AlgebraicGeometry

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X : Scheme.{u}}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] (e : ℕ)
  (he : ringChar Λ = ringChar Λ' * e)

/-- The morphism from the Kummer sequence of level `n = ringChar Λ` pulled back along
`φ : C ⟶ 𝔾ₘ`, with coefficients `Λ`, to the Kummer sequence of level `n' = ringChar Λ'` pulled
back along `φ`, with coefficients `Λ'` and scalars restricted to `Λ`: the `e`-th power maps
(`n = n' e`) followed by the change of coefficients along `ρ`. -/
noncomputable def kummerPullbackChangeMap {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : C ⟶ X.gmSheaf) :
    ((X.kummerSequence (ringChar Λ)).pullback φ).map (extendScalars Λ X) ⟶
      ((X.kummerSequence (ringChar Λ')).pullback φ).map
        (extendScalars Λ' X ⋙ Sheaf.restrictScalars X.smallEtaleTopology ρ) :=
  (extendScalars Λ X).mapShortComplex.map
      (ShortComplex.pullbackMapOfHom (kummerSequencePowMap _ e _ he) φ φ (Category.comp_id _)) ≫
    ((X.kummerSequence (ringChar Λ')).pullback φ).mapNatTrans (extendScalarsChangeMap ρ X)

/-- **The change of coefficients of the Kummer boundary**: the connecting morphism of the
pulled back Kummer sequence with coefficients `Λ`, followed by the change of coefficients
`μ_n ⊗ Λ ⟶ μ_{n'} ⊗ Λ'` (the `e`-th power map and `ρ`), is the change of coefficients
`Λ ⊗ C ⟶ Λ' ⊗ C` followed by the connecting morphism of the sequence with coefficients `Λ'`,
with scalars restricted to `Λ`. -/
lemma kummerδ_comp_changeMap {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : C ⟶ X.gmSheaf)
    (hC : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj C)) :
    kummerδ Λ φ hC ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((extendScalars Λ X).map (rootsOfUnityPow _ e _ he) ≫
          (extendScalarsChangeMap ρ X).app _))⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor _ 0).map ((extendScalarsChangeMap ρ X).app C) ≫
        ((shortExact_kummerSequence_pullback_map_extendScalars Λ' φ hC).map_of_exact
          (Sheaf.restrictScalars X.smallEtaleTopology ρ)).singleδ := by
  have h : kummerδ Λ φ hC ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((extendScalars Λ X).map (rootsOfUnityPow _ e _ he) ≫
          (extendScalarsChangeMap ρ X).app _))⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor _ 0).map ((extendScalars Λ X).map (𝟙 C) ≫
          (extendScalarsChangeMap ρ X).app C) ≫
        ((shortExact_kummerSequence_pullback_map_extendScalars Λ' φ hC).map_of_exact
          (Sheaf.restrictScalars X.smallEtaleTopology ρ)).singleδ :=
    (ShortComplex.ShortExact.singleTriangle.map
    (shortExact_kummerSequence_pullback_map_extendScalars Λ φ hC)
    ((shortExact_kummerSequence_pullback_map_extendScalars Λ' φ hC).map_of_exact
      (Sheaf.restrictScalars X.smallEtaleTopology ρ))
    (kummerPullbackChangeMap ρ e he φ)).comm₃
  rwa [CategoryTheory.Functor.map_id, Category.id_comp] at h

/-- `AlgebraicGeometry.Etale.kummerδ_comp_changeMap`, with the restriction of scalars of the
connecting morphism of the sequence with coefficients `Λ'`. -/
lemma kummerδ_comp_changeMap_restrictScalars {C : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (φ : C ⟶ X.gmSheaf)
    (hC : ∀ x : X, Projective ((X.uliftPointSmallEtale x).sheafFiber.obj C)) :
    kummerδ Λ φ hC ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((extendScalars Λ X).map (rootsOfUnityPow _ e _ he) ≫
          (extendScalarsChangeMap ρ X).app _) ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          _)⟦(1 : ℤ)⟧' =
      (DerivedCategory.singleFunctor _ 0).map ((extendScalarsChangeMap ρ X).app C) ≫
        ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          _ ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (kummerδ Λ' φ hC) ≫
          ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).commShiftIso
            (1 : ℤ)).hom.app _ := by
  have h₁ := kummerδ_comp_changeMap ρ e he φ hC
  have h₂ := (shortExact_kummerSequence_pullback_map_extendScalars Λ' φ hC).mapShiftedHom_singleδ
    (Sheaf.restrictScalars X.smallEtaleTopology ρ)
  simp only [ShiftedHom.map] at h₂
  have h₂' : (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (kummerδ Λ' φ hC) ≫
      ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).commShiftIso (1 : ℤ)).hom.app _ =
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).hom.app
          ((extendScalars Λ' X).obj C) ≫
        ((shortExact_kummerSequence_pullback_map_extendScalars Λ' φ hC).map_of_exact
          (Sheaf.restrictScalars X.smallEtaleTopology ρ)).singleδ ≫
          (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor
            0).inv.app
              ((extendScalars Λ' X).obj (X.rootsOfUnitySheaf (ringChar Λ'))))⟦(1 : ℤ)⟧' :=
    h₂
  calc _ = (kummerδ Λ φ hC ≫ ((DerivedCategory.singleFunctor _ 0).map
        ((extendScalars Λ X).map (rootsOfUnityPow _ e _ he) ≫
          (extendScalarsChangeMap ρ X).app _))⟦(1 : ℤ)⟧') ≫
        (((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app
          _)⟦(1 : ℤ)⟧' := by rw [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [h₁, h₂', Iso.inv_hom_id_app_assoc]
      exact Category.assoc _ _ _

end AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') (X : Scheme.{u})
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] [NeZero (ringChar Λ)]
  [NeZero (ringChar Λ')] (e : ℕ) (he : ringChar Λ = ringChar Λ' * e)

/-- The change of coefficients `Λ_X ⟶ Res Λ'_X` of the constant complexes, through the
identifications `Λ_X ≅ (Λ ⊗ ℤ)[0]` of the Kummer classes
(`AlgebraicGeometry.Etale.constantComplexIsoSingleFunctorExtendScalarsInt`). -/
noncomputable def constantComplexChangeMap :
    constantComplex Λ X ⟶
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj (constantComplex Λ' X) :=
  (constantComplexIsoSingleFunctorExtendScalarsInt X Λ).hom ≫
    (DerivedCategory.singleFunctor _ 0).map ((extendScalarsChangeMap ρ X).app _) ≫
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map
          (constantComplexIsoSingleFunctorExtendScalarsInt X Λ').inv

/-- The change of coefficients `Λ_X(1) ⟶ Res Λ'_X(1)` of the Tate twists: through
`Λ_X(1) ≅ (μ_n ⊗ Λ)[0]` (`AlgebraicGeometry.Etale.tateTwistObjectOneIso`), the `e`-th power map
`μ_n ⟶ μ_{n'}` (`n = n' e`) followed by the change of coefficients `μ_{n'} ⊗ Λ ⟶ μ_{n'} ⊗ Λ'`. -/
noncomputable def tateTwistObjectOneChangeMap :
    tateTwistObject Λ X 1 ⟶
      (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).obj (tateTwistObject Λ' X 1) :=
  (tateTwistObjectOneIso X Λ).hom ≫
    (DerivedCategory.singleFunctor _ 0).map
      ((extendScalars Λ X).map (rootsOfUnityPow _ e _ he) ≫ (extendScalarsChangeMap ρ X).app _) ≫
      ((Sheaf.restrictScalars X.smallEtaleTopology ρ).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (tateTwistObjectOneIso X Λ').inv

/-- **The change of coefficients of a Kummer class is the Kummer class**, with scalars restricted:
for `ρ : Λ →+* Λ'` with `n = n' e`, the Kummer class `κ(u) : Λ_X ⟶ Λ_X(1)[1]` followed by the
change of coefficients of the Tate twist (`tateTwistObjectOneChangeMap`, the `e`-th power map)
is the change of coefficients of the constant complex followed by the restriction of scalars of
the Kummer class `κ(u) : Λ'_X ⟶ Λ'_X(1)[1]`. -/
theorem kummerClassOf_comp_tateTwistObjectOneChangeMap (v : Γ(X, ⊤)ˣ) :
    kummerClassOf X Λ v ≫ (tateTwistObjectOneChangeMap ρ X e he)⟦(1 : ℤ)⟧' =
      constantComplexChangeMap ρ X ≫
        (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).map (kummerClassOf X Λ' v) ≫
        ((Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ).commShiftIso (1 : ℤ)).hom.app _ := by
  have hK := kummerδ_comp_changeMap_restrictScalars ρ e he (unitToGmSheaf v)
    (fun x ↦ projective_sheafFiber_constantSheafInt (X.uliftPointSmallEtale x))
  simp only [Functor.map_comp, Category.assoc] at hK
  simp only [kummerClassOf_def, tateTwistObjectOneChangeMap, constantComplexChangeMap,
    Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc (shiftFunctor _ (1 : ℤ)) (tateTwistObjectOneIso X Λ).inv,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
    ← Functor.map_comp_assoc (Sheaf.derivedRestrictScalars X.smallEtaleTopology ρ)
      (constantComplexIsoSingleFunctorExtendScalarsInt X Λ').inv, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp,
    Functor.commShiftIso_hom_naturality, reassoc_of% hK]

/-- The defining formula of `tateTwistObjectOneChangeMap` (stated through its equation lemma, so
that it is literally the stored body: re-elaborating the body costs a large kernel check). -/
theorem tateTwistObjectOneChangeMap_eq : type_of% @tateTwistObjectOneChangeMap.eq_1.{u} :=
  @tateTwistObjectOneChangeMap.eq_1.{u}

-- the body is heavy: only access it through `tateTwistObjectOneChangeMap_eq`
attribute [irreducible] tateTwistObjectOneChangeMap

end AlgebraicGeometry.Etale
