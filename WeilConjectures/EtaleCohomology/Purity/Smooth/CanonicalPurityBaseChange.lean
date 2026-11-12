/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductAppend
public import WeilConjectures.EtaleCohomology.Purity.Smooth.WeilEquivariance
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekTensorMapUnit
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekBaseChangeMapComparison
public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.TensorMapBaseChange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.LowerShriekTraceCounitBaseChange

/-!
# Compatibility of the canonical purity map with base change

For `f : X ⟶ Y` smooth separated of relative dimension `d`, the *canonical purity map*
`γ_f(K) : Lf^* K(d)[2d] ⟶ Rf^! K` (`AlgebraicGeometry.Etale.canonicalSmoothPurityMap`) is the
composite of the twist reassociation, the inverse of the canonical orientation
`θ_f : ω_f ≅ Λ_X(d)[2d]` (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`), the symmetry
and the canonical tensor map `ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K`
(`AlgebraicGeometry.Etale.dualizingComplexTensorMap`). Blueprint
`proposition-compatibility-purity-base-change` asserts `g'^* γ_f(K) = γ_{f'}(g^* K)` for a
cartesian square (`AlgebraicGeometry.Etale.canonicalSmoothPurityMap_baseChange`).

Each factor of `γ_f` commutes with base change: the orientation
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange`), the tensor map
(`AlgebraicGeometry.Etale.dualizingComplexTensorMap_baseChange`), the symmetry
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_derivedTensorBraiding_comp_tensorComparison`)
and the twist reassociation
(`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_twistShiftObjIso_hom`).

## Main statements

- `AlgebraicGeometry.Etale.canonicalSmoothPurityMap_baseChange`
  (`proposition-compatibility-purity-base-change`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory

open scoped CategoryTheory.Functor

-- The instances of `WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientation`.
attribute [local instance high] SymmetricCategory.toBraidedCategory

namespace AlgebraicGeometry.Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasKummerClass Λ]
  [HasKummerClass.IsNormalized Λ]

omit [CommRing Λ] [Finite Λ] [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] in
/-- The monoidal computation behind `AlgebraicGeometry.Etale.canonicalSmoothPurityMap_unit`. -/
private lemma unit_aux {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    {A W O T : C} (e : A ⟶ 𝟙_ C) (ψ : T ⟶ A ⊗ W) (ψ₁ : W ⟶ 𝟙_ C ⊗ W) (t : T ⟶ W)
    (φ : W ⟶ O) (hn : t ≫ ψ₁ = ψ ≫ e ▷ W) (h₁ : ψ₁ ≫ (λ_ W).hom = 𝟙 _) :
    ψ ≫ A ◁ φ ≫ (β_ A O).hom ≫ O ◁ e ≫ (ρ_ O).hom = t ≫ φ := by
  rw [← BraidedCategory.braiding_naturality_left_assoc, braiding_rightUnitor,
    whisker_exchange_assoc, leftUnitor_naturality, ← reassoc_of% hn, reassoc_of% h₁]

omit [CommRing Λ] [Finite Λ] [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] in
/-- The monoidal computation behind
`AlgebraicGeometry.Etale.canonicalSmoothPurityMap_naturality`. -/
private lemma nat_aux {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    {A A' W O T T' R R' : C} (v : A ⟶ A') (ψ : T ⟶ A ⊗ W) (ψ' : T' ⟶ A' ⊗ W) (t : T ⟶ T')
    (φ : W ⟶ O) (τ : O ⊗ A ⟶ R) (τ' : O ⊗ A' ⟶ R') (r : R ⟶ R')
    (hn : t ≫ ψ' = ψ ≫ v ▷ W) (hτ : τ ≫ r = O ◁ v ≫ τ') :
    (ψ ≫ A ◁ φ ≫ (β_ A O).hom ≫ τ) ≫ r = t ≫ ψ' ≫ A' ◁ φ ≫ (β_ A' O).hom ≫ τ' := by
  rw [reassoc_of% hn, Category.assoc, Category.assoc, Category.assoc, hτ,
    ← BraidedCategory.braiding_naturality_left_assoc, whisker_exchange_assoc]

section Map

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (d : ℕ) [SmoothOfRelativeDimension d f] [IsSeparated f]
  [HasCompactification f] [HasInvertibleExponent Λ X] {k : Type u} [Field k]
  (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]

/-- The canonical purity map `γ_f(K) : Lf^* K(d)[2d] ⟶ Rf^! K`:
`Lf^* K(d)[2d] ≅ Lf^* K ⊗ᴸ Λ_X(d)[2d] ≅ Lf^* K ⊗ᴸ ω_f ≅ ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K`, through the
canonical orientation `θ_f` (`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso`) and the
canonical tensor map (`AlgebraicGeometry.Etale.dualizingComplexTensorMap`). -/
noncomputable def canonicalSmoothPurityMap
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) ⟶ (R(f)^![Λ]).obj K :=
  (twistShiftObjIso Λ X d _).hom ≫
    ((derivedTensor _ X).obj _).map (dualizingComplexTwistShiftIso Λ f d aY).inv ≫
      (derivedTensorBraidingIso _ X _ _).hom ≫ dualizingComplexTensorMap Λ f K

/-- At `K = Λ_Y`, the canonical purity map is the inverse of the canonical orientation, read
through `Lf^* Λ_Y ≅ Λ_X`. -/
lemma canonicalSmoothPurityMap_unit :
    canonicalSmoothPurityMap Λ f d aY (𝟙_ _) =
      (twistShift Λ X d).map (leftDerivedUpperStarUnitIso _ f).hom ≫
        (dualizingComplexTwistShiftIso Λ f d aY).inv := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have hT : dualizingComplexTensorMap Λ f (𝟙_ _) =
      dualizingComplex Λ f ◁ (leftDerivedUpperStarUnitIso _ f).hom ≫ (ρ_ _).hom :=
    lowerShriekRightAdjointUnitTensorMap_unit (rightDerivedUpperShriekAdjunction Λ f)
  have hβ (M N : DerivedCategoryModule Λ X) :
      (derivedTensorBraidingIso _ X M N).hom = (β_ M N).hom := rfl
  -- `Λ_X(d)[2d] ≅ Λ_X ⊗ᴸ Λ_X(d)[2d] ⟶ Λ_X(d)[2d]` is the identity
  have h1 : (twistShiftObjIso Λ X d (𝟙_ _)).hom ≫ (λ_ _).hom = 𝟙 _ := by
    have hc := derivedTensorLeftUnitor_commShift (A := ModuleCat.{u + 1} Λ) (X := X)
      (tateObject Λ X d) (2 * d)
    simp only [twistShiftObjIso, twistShiftConstantComplexIso, Iso.trans_hom, Iso.symm_hom,
      Iso.app_inv, Category.assoc]
    change _ ≫ 𝟙_ _ ◁ ((λ_ (tateObject Λ X d)).inv)⟦2 * (d : ℤ)⟧' ≫ _ = _
    rw [leftUnitor_naturality]
    erw [← reassoc_of% hc]
    rw [Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
    erw [Iso.hom_inv_id, CategoryTheory.Functor.map_id]
    rfl
  have hn := twistShiftObjIso_hom_naturality Λ (d : ℤ) (leftDerivedUpperStarUnitIso _ f).hom
  rw [canonicalSmoothPurityMap, hT, hβ]
  change _ ≫ _ ◁ _ ≫ _ = _
  exact unit_aux (leftDerivedUpperStarUnitIso _ f).hom (twistShiftObjIso Λ X d _).hom
    (twistShiftObjIso Λ X d (𝟙_ _)).hom
    ((twistShift Λ X d).map (leftDerivedUpperStarUnitIso _ f).hom)
    (dualizingComplexTwistShiftIso Λ f d aY).inv hn h1

/-- The canonical purity map is natural in `K`. -/
lemma canonicalSmoothPurityMap_naturality
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : K ⟶ K') :
    canonicalSmoothPurityMap Λ f d aY K ≫ (R(f)^![Λ]).map φ =
      (twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map φ) ≫
        canonicalSmoothPurityMap Λ f d aY K' := by
  let := _root_.DerivedCategory.braidedCategory' (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have hT :=
    lowerShriekRightAdjointUnitTensorMap_naturality (rightDerivedUpperShriekAdjunction Λ f) φ
  have hn := twistShiftObjIso_hom_naturality Λ (d : ℤ) ((L((f)^*[ModuleCat.{u + 1} Λ])).map φ)
  exact nat_aux _ _ _ _ _ _ _ _ hn hT

end Map

section TwistShift

variable {X Y : Scheme.{u}} [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

omit [Finite Λ] [HasKummerClass.IsNormalized Λ] in
/-- The identification `Lf^*(K(m)[2m]) ≅ (Lf^* K)(m)[2m]`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftIso`) is natural in `K`. -/
@[reassoc]
lemma leftDerivedUpperStarTwistShiftIso_hom_naturality (f : X ⟶ Y) (m : ℤ)
    {K K' : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (v : K ⟶ K') :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map ((twistShift Λ Y m).map v) ≫
        (leftDerivedUpperStarTwistShiftIso Λ f m K').hom =
      (leftDerivedUpperStarTwistShiftIso Λ f m K).hom ≫
        (twistShift Λ X m).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map v) := by
  simp only [leftDerivedUpperStarTwistShiftIso, twistShift, tateTwist, Iso.trans_hom,
    Iso.app_hom, Functor.mapIso_hom, Functor.comp_map, Functor.flip_obj_map, Category.assoc]
  rw [Functor.commShiftIso_hom_naturality_assoc, ← Functor.map_comp, ← Functor.map_comp]
  congr 2
  rw [reassoc_of% leftDerivedUpperStarTensorIso_hom_naturality_left, Category.assoc,
    NatTrans.naturality]

omit [Finite Λ] [HasKummerClass.IsNormalized Λ] in
/-- The twist reassociation `M(m)[2m] ≅ M ⊗ᴸ Λ_Y(m)[2m]`
(`AlgebraicGeometry.Etale.twistShiftObjIso`) commutes with the derived pullback: through the
tensor structure of `Lf^*` and `Lf^*(Λ_Y(m)[2m]) ≅ Λ_X(m)[2m]`, its pullback is the twist
reassociation of `Lf^* M`:
```
Lf^*(M(m)[2m]) ──Lf^* r──▶ Lf^*(M ⊗ Λ_Y(m)[2m]) ──≅──▶ Lf^* M ⊗ Lf^*(Λ_Y(m)[2m])
      ≅ │                                                       │ ≅
        ▼                                                       ▼
(Lf^* M)(m)[2m] ───────────────r──────────────▶ Lf^* M ⊗ Λ_X(m)[2m]
```
-/
lemma leftDerivedUpperStar_map_twistShiftObjIso_hom (f : X ⟶ Y) (m : ℤ)
    (M : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (twistShiftObjIso Λ Y m M).hom ≫
        (leftDerivedUpperStarTensorIso _ f M _).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)).map
            (twistShiftConstantComplexBaseChangeIso Λ f m).hom =
      (leftDerivedUpperStarTwistShiftIso Λ f m M).hom ≫
        (twistShiftObjIso Λ X m ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)).hom := by
  have hs := leftDerivedUpperStarTensorComparison_shift_right (ModuleCat.{u + 1} Λ) f M
    (tateObject Λ Y m) (2 * m)
  have hn := leftDerivedUpperStarTensorIso_hom_naturality_right f M
    (twistShiftConstantComplexIso Λ Y m).inv
  simp only [← leftDerivedUpperStarTensorIso_hom] at hs
  have hq := ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
    ((L((f)^*[ModuleCat.{u + 1} Λ])).obj M)).commShiftIso_inv_naturality
      (leftDerivedUpperStarTateObjectIso f m).hom (2 * m)
  simp only [twistShiftObjIso, twistShiftConstantComplexBaseChangeIso,
    leftDerivedUpperStarTwistShiftIso, leftDerivedUpperStarTateShiftIso, Iso.trans_hom,
    Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rw [reassoc_of% hn, ← Functor.map_comp_assoc _ ((L((f)^*[ModuleCat.{u + 1} Λ])).map _),
    ← Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
    CategoryTheory.Functor.map_id, Category.id_comp, reassoc_of% hq]
  rw [← cancel_epi ((L((f)^*[ModuleCat.{u + 1} Λ])).map
    ((((derivedTensor (ModuleCat.{u + 1} Λ) Y).obj M).commShiftIso (2 * m)).hom.app
      (tateObject Λ Y m))), ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  erw [reassoc_of% hs]
  rw [Iso.hom_inv_id_app_assoc]

end TwistShift

omit [CommRing Λ] [Finite Λ] [HasKummerClass Λ] [HasKummerClass.IsNormalized Λ] in
/-- The monoidal computation behind
`AlgebraicGeometry.Etale.canonicalSmoothPurityMap_baseChange`. -/
private lemma baseChange_aux {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]
    {S P₁ P₂ P₃ Q R A T W A' T' W' Z : C} (a : S ⟶ P₁) (b : P₁ ⟶ P₂) (bb : P₂ ⟶ P₃)
    (lμ : P₃ ⟶ Q) (bK : Q ⟶ R) (τ₁ : P₁ ⟶ A ⊗ T) (τ₂ : P₂ ⟶ A ⊗ W) (τ₃ : P₃ ⟶ W ⊗ A)
    (lθ : T ⟶ W) (vT : T ⟶ T') (vω : W ⟶ W') (θ : T' ⟶ W') (c : A ⟶ A')
    (μ : W' ⊗ A' ⟶ R) (Ψ : S ⟶ Z) (t : Z ⟶ A' ⊗ T')
    (hΨ : Ψ ≫ t = a ≫ τ₁ ≫ A ◁ vT ≫ c ▷ T') (h₂ : b ≫ τ₂ = τ₁ ≫ A ◁ lθ)
    (h₃ : bb ≫ τ₃ = τ₂ ≫ (β_ A W).hom) (h₄ : lμ ≫ bK = τ₃ ≫ vω ▷ A ≫ W' ◁ c ≫ μ)
    (h₅ : lθ ≫ vω = vT ≫ θ) :
    (a ≫ b ≫ bb ≫ lμ) ≫ bK = Ψ ≫ t ≫ A' ◁ θ ≫ (β_ A' W').hom ≫ μ := by
  rw [reassoc_of% hΨ]
  simp only [Category.assoc]
  rw [h₄, reassoc_of% h₃, reassoc_of% h₂, ← BraidedCategory.braiding_naturality_right_assoc,
    ← BraidedCategory.braiding_naturality_left_assoc, ← whiskerLeft_comp_assoc, h₅,
    whiskerLeft_comp_assoc, whisker_exchange_assoc]

section BaseChange

variable {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
  {f : X ⟶ Y} {g : Y' ⟶ Y} (d : ℕ) [SmoothOfRelativeDimension d f]
  [SmoothOfRelativeDimension d f'] [IsSeparated f] [IsSeparated f'] [HasCompactification f]
  [HasCompactification f'] [QuasiCompact f'] [HasInvertibleExponent Λ X]
  [HasInvertibleExponent Λ X'] {k k' : Type u} [Field k] [Field k']

/-- Blueprint `proposition-compatibility-purity-base-change` (formerly `sk-prop-sp-purity-bc`,
`chap-Smooth-purity`): compatibility of purity with base change.

For a cartesian square `g' ≫ f = f' ≫ g` with `f` and `f'` smooth separated of relative
dimension `d` and `K ∈ D(Y_ét, Λ)`, identify the sources of the canonical purity maps by
`Lg'^* Lf^* ≅ Lf'^* Lg^*` (`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftBaseChangeIso`)
and the targets by the exceptional base change map
(`AlgebraicGeometry.Etale.upperShriekBaseChangeMap`). Then `g'^* γ_f(K) = γ_{f'}(g^* K)`.

The proof composes the base change of the orientation
(`AlgebraicGeometry.Etale.dualizingComplexTwistShiftIso_baseChange`), of the tensor map
(`AlgebraicGeometry.Etale.dualizingComplexTensorMap_baseChange`), of the symmetry and of the
twist reassociation. -/
theorem canonicalSmoothPurityMap_baseChange (sq : IsPullback g' f' f g)
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY]
    (aY' : Y' ⟶ Spec (.of k')) [IsSeparated aY'] [LocallyOfFiniteType aY']
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    (L((g')^*[ModuleCat.{u + 1} Λ])).map (canonicalSmoothPurityMap Λ f d aY K) ≫
        (upperShriekBaseChangeMap Λ sq).app K =
      (leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq.toCommSq K).hom ≫
        canonicalSmoothPurityMap Λ f' d aY' ((L((g)^*[ModuleCat.{u + 1} Λ])).obj K) := by
  let := _root_.DerivedCategory.braidedCategory'
    (Sheaf X'.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  have : QuasiCompact f := HasCompactification.quasiCompact_of_locallyOfFiniteType f aY
  -- the orientations
  have hO := dualizingComplexTwistShiftIso_baseChange Λ d sq aY aY'
  rw [← twistShiftConstantComplexBaseChangeIso_hom] at hO
  have h₅ : (L((g')^*[ModuleCat.{u + 1} Λ])).map (dualizingComplexTwistShiftIso Λ f d aY).inv ≫
      (upperShriekBaseChangeMap Λ sq).app (constantComplex Λ Y) ≫
        (R(f')^![Λ]).map (leftDerivedUpperStarUnitIso _ g).hom =
      (twistShiftConstantComplexBaseChangeIso Λ g' d).hom ≫
        (dualizingComplexTwistShiftIso Λ f' d aY').inv := by
    rw [← cancel_mono (dualizingComplexTwistShiftIso Λ f' d aY').hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    rw [hO, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  -- the twist reassociations
  have hΨ := leftDerivedUpperStar_map_twistShiftObjIso_hom Λ g' d
    ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)
  have hn := twistShiftObjIso_hom_naturality Λ (d : ℤ)
    (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq K)
  have hΨ' : (leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq.toCommSq K).hom ≫
      (twistShiftObjIso Λ X' d _).hom =
      (L((g')^*[ModuleCat.{u + 1} Λ])).map (twistShiftObjIso Λ X d _).hom ≫
        (leftDerivedUpperStarTensorIso _ g' _ _).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) X').obj _).map
            (twistShiftConstantComplexBaseChangeIso Λ g' d).hom ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) X').map
            (derivedSquareUpperStarIsoInvApp (ModuleCat.{u + 1} Λ) sq.toCommSq K)).app _ := by
    simp only [leftDerivedUpperStarTwistShiftBaseChangeIso, Iso.trans_hom, Functor.mapIso_hom,
      Category.assoc]
    erw [hn]
    rw [reassoc_of% hΨ]
  -- the tensor structure, the braiding and the tensor maps
  have h₂ := leftDerivedUpperStarTensorIso_hom_naturality_right g'
    ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) (dualizingComplexTwistShiftIso Λ f d aY).inv
  have h₃ := leftDerivedUpperStar_map_derivedTensorBraiding_comp_tensorComparison g'
    ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) (dualizingComplex Λ f)
  have h₄ := dualizingComplexTensorMap_baseChange sq K
  rw [canonicalSmoothPurityMap, canonicalSmoothPurityMap, Functor.map_comp, Functor.map_comp,
    Functor.map_comp]
  exact baseChange_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hΨ' h₂ h₃ h₄ h₅

end BaseChange

end AlgebraicGeometry.Etale
