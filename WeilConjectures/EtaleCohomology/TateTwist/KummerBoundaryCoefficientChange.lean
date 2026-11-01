/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.TateTwist.KummerClass
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChangeSingle
public import WeilConjectures.EtaleCohomology.TateTwist.KummerLevelIndependence

/-!
# The Kummer boundary under a change of coefficients

Let `ρ : Λ →+* Λ'` be a morphism of commutative rings whose characteristics satisfy
`n = n' e` (for instance the reduction `𝒪_E ⧸ ℓⁿ⁺¹ ⟶ 𝒪_E ⧸ ℓⁿ`, with `e = ℓ`). The Kummer
sequences of `n` and `n'` are related by the `e`-th power maps
(`AlgebraicGeometry.Scheme.kummerSequencePowMap`), and extension of scalars along `ρ` gives a
morphism `Λ ⊗ F ⟶ Λ' ⊗ F` of sheaves of `Λ`-modules
(`AlgebraicGeometry.Etale.extendScalarsChangeMap`). Together they give a morphism from the
pulled back Kummer sequence with coefficients `Λ` to the one with coefficients `Λ'`, with scalars
restricted to `Λ`, so that the connecting morphisms correspond
(`AlgebraicGeometry.Etale.kummerδ_comp_changeMap`,
`AlgebraicGeometry.Etale.kummerδ_comp_changeMap_restrictScalars`).
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


end AlgebraicGeometry.Etale

namespace CategoryTheory

/-- In a category with a shift, `a ≫ (m₁ ≫ i₁)⟦1⟧' = m₃ ≫ i₃ ≫ d` follows from
`a ≫ m₁⟦1⟧' = m₃ ≫ δ` and `i₃' ≫ d = δ' ≫ i₁'⟦1⟧'`, where the primed data agree with the
unprimed ones up to the equalities of their objects. (The objects are kept apart so that the
lemma can be instantiated with two presentations of the same objects without unfolding them.) -/
lemma shift_map_comp_eq_of_comp_eq_of_heq {T : Type*} [Category* T] [HasShift T ℤ]
    {A B R₁ R₃ R₁' R₃' U V : T} {a : A ⟶ B⟦(1 : ℤ)⟧} {m₁ : B ⟶ R₁} {i₁ : R₁ ⟶ V}
    {m₃ : A ⟶ R₃} {i₃ : R₃ ⟶ U} {d : U ⟶ V⟦(1 : ℤ)⟧} {δ : R₃ ⟶ R₁⟦(1 : ℤ)⟧}
    {δ' : R₃' ⟶ R₁'⟦(1 : ℤ)⟧} {i₁' : R₁' ⟶ V} {i₃' : R₃' ⟶ U}
    (h : a ≫ m₁⟦(1 : ℤ)⟧' = m₃ ≫ δ) (k : i₃' ≫ d = δ' ≫ i₁'⟦(1 : ℤ)⟧')
    (h₃ : R₃ = R₃') (h₁ : R₁ = R₁') (hδ : HEq δ δ') (hi₁ : HEq i₁ i₁') (hi₃ : HEq i₃ i₃') :
    a ≫ (m₁ ≫ i₁)⟦(1 : ℤ)⟧' = m₃ ≫ i₃ ≫ d := by
  subst h₃ h₁
  obtain rfl := eq_of_heq hδ
  obtain rfl := eq_of_heq hi₁
  obtain rfl := eq_of_heq hi₃
  rw [Functor.map_comp, reassoc_of% h, k]

end CategoryTheory

namespace AlgebraicGeometry.Etale

open Scheme

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ') {X : Scheme.{u}}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] (e : ℕ)
  (he : ringChar Λ = ringChar Λ' * e)

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
            (1 : ℤ)).hom.app _ :=
  shift_map_comp_eq_of_comp_eq_of_heq (kummerδ_comp_changeMap ρ e he φ hC)
    ((shortExact_kummerSequence_pullback_map_extendScalars Λ' φ hC
      ).mapDerivedCategorySingleFunctor_inv_comp_map_singleδ_of_heq
      (Sheaf.restrictScalars X.smallEtaleTopology ρ)
      (Z₁ := (extendScalars Λ' X).obj (X.rootsOfUnitySheaf (ringChar Λ')))
      (Z₃ := (extendScalars Λ' X).obj C) rfl rfl (kummerδ Λ' φ hC) HEq.rfl _ HEq.rfl)
    rfl rfl HEq.rfl HEq.rfl HEq.rfl

end AlgebraicGeometry.Etale
