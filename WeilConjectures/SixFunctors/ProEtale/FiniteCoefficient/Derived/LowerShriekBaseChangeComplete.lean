/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.Completion
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekBaseChange

/-!
# Complete pro-étale compact-support base change

Let `Λ` be a commutative ring and `ϖ ∈ Λ` a nonzerodivisor such that the quotients `Λ/ϖⁿ` are
finite (for instance `Λ = 𝒪_E` with a uniformizer `ϖ`, so that `Λ/ϖⁿ = A_{E,n}`; this is the adic
coefficient datum of blueprint `def-weil-pbc-adic-coefficient-datum` for a principal ideal
`I = (ϖ)`). For a cartesian square
```
X' --g'--> X
|f'        |f
Y' --g---> Y
```
with `f` separated of finite type, a compactification `c` of `f` and its base change, and a
complex `K` of pro-étale sheaves of `Λ`-modules on `X` which is derived `ϖ`-complete and whose
reductions `K_n = K ⊗ᴸ_Λ Λ/ϖⁿ` are of étale origin, the completed compact-support exchange map

`Ex^comp_!(K) : Lg^*_comp Rf_! K ⟶ Rf'_! Lg'^*_comp K`

is an isomorphism (blueprint `thm-cbc-complete-proetale`).

## The completed operations

As at the integral stage of the étale model
(`WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Integral`), the operations on
derived complete objects are the derived limits of their finite reductions, that is, the derived
completions (`DerivedCategory.derivedCompletion`) of the plain operations of `D(X_proét, Λ)`: the
completed pullback is `Lg^*_comp K = (Lg^* K)^` (blueprint `def-weil-pbc-completed-pullback`: "the
comparison from ordinary pullback is the completion map of `Lg^*K`"), and the completed exchange
map is the derived completion of the plain compact-support exchange map `Ex_!(c)`
(`AlgebraicGeometry.ProEtale.completedRightDerivedLowerShriekOfCompactificationBaseChangeMap`,
blueprint `def-cbc-completed-exchange-map`).

## Proof

The reduction modulo `ϖ` of `Ex_!(c)` at `K` is, up to isomorphism of arrows, the restriction of
scalars of the exchange map `Ex_!(c)` over the finite ring `Λ/ϖ` at the reduction `K_1`
(`nonempty_arrowIso_reductionModIdeal_rightDerivedLowerShriekOfCompactificationBaseChangeMap`,
the compatibility of the exchange transformations with coefficient reduction of blueprint
`lem-fix-operation-reduction`). The latter is an isomorphism by the finite-level pro-étale
compact-support base change for complexes of étale origin
(`AlgebraicGeometry.ProEtale.isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app`,
blueprint `thm-cbc-finite-level-proetale`). Hence the cone of `Ex_!(c)` at `K` has vanishing
reduction, so `ϖ` acts invertibly on it
(`AlgebraicGeometry.ProEtale.isIso_smul_id_of_isZero_reductionModIdeal`), and the derived
completion inverts such morphisms
(`DerivedCategory.isIso_derivedCompletion_map_of_smulInvertible`). This is the argument of the
blueprint proof (completed proper base change for the proper part, which is proved in the same
way, and the completed extension-by-zero comparison), carried out for the composite at once.

## Main definitions

- `AlgebraicGeometry.ProEtale.reductionModIdeal Λ X J`: the reduction `K ↦ K ⊗ᴸ (Λ/J)_X` on
  `D(X_proét, Λ)`.
- `AlgebraicGeometry.ProEtale.completedRightDerivedLowerShriekOfCompactificationBaseChangeMap`:
  the completed compact-support exchange map (`def-cbc-completed-exchange-map`).

## Main statements

- `isIso_completedRightDerivedLowerShriekOfCompactificationBaseChangeMap_app`
  (`thm-cbc-complete-proetale`).
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

open Scheme

set_option hygiene false in
/-- The derived category `D(X_proét, Λ)` of pro-étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))

/-! ### Reduction of coefficients -/

section Reduction

/- The monoidal structure of `D(X_proét, Λ)` is taken from the fields of the constant
`DerivedCategory.sheafTensorStructure`, as in the files on derived completeness (see the
implementation notes of `WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`). -/
attribute [-instance] _root_.DerivedCategory.commShift₂CurriedTensor
  _root_.DerivedCategory.commShiftTensorLeft _root_.DerivedCategory.commShiftTensorRight
  _root_.DerivedCategory.isTriangulated_tensorLeft
  _root_.DerivedCategory.isTriangulated_tensorRight
  _root_.DerivedCategory.monoidalPreadditive _root_.DerivedCategory.monoidalLinear

variable (Λ : Type (u + 1)) [CommRing Λ] (X : Scheme.{u})

noncomputable local instance (priority := high) : MonoidalCategory 𝐃(X, Λ) :=
  (_root_.DerivedCategory.sheafTensorStructure (Scheme.ProEt.topology X) Λ).monoidalCategory

noncomputable local instance (priority := high) : MonoidalPreadditive 𝐃(X, Λ) :=
  (_root_.DerivedCategory.sheafTensorStructure (Scheme.ProEt.topology X) Λ).monoidalPreadditive

noncomputable local instance (priority := high) : MonoidalLinear Λ 𝐃(X, Λ) :=
  (_root_.DerivedCategory.sheafTensorStructure (Scheme.ProEt.topology X) Λ).monoidalLinear

noncomputable local instance (priority := high) : (curriedTensor 𝐃(X, Λ)).CommShift₂Int :=
  (_root_.DerivedCategory.sheafTensorStructure (Scheme.ProEt.topology X) Λ).commShift₂

noncomputable local instance (priority := high) (K : 𝐃(X, Λ)) :
    ((curriedTensor 𝐃(X, Λ)).obj K).IsTriangulated :=
  (_root_.DerivedCategory.sheafTensorStructure (Scheme.ProEt.topology X)
    Λ).isTriangulated_tensorLeft K

noncomputable local instance (priority := high) (K : 𝐃(X, Λ)) :
    ((curriedTensor 𝐃(X, Λ)).flip.obj K).IsTriangulated :=
  (_root_.DerivedCategory.sheafTensorStructure (Scheme.ProEt.topology X)
    Λ).isTriangulated_tensorRight K

/-- Reduction of coefficients along a quotient of the coefficient ring: the functor
`K ↦ K ⊗ᴸ (Λ/J)_X` on `D(X_proét, Λ)`. For `Λ = 𝒪_E` and `J = (ϖⁿ)` this is the finite
reduction `K ↦ K_n` of the adic formalism. -/
noncomputable def reductionModIdeal (J : Ideal Λ) : 𝐃(X, Λ) ⥤ 𝐃(X, Λ) :=
  (curriedTensor 𝐃(X, Λ)).flip.obj
    ((_root_.DerivedCategory.singleFunctor _ 0).obj
      ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (Λ ⧸ J))))

/-- The reduction `K ↦ K ⊗ᴸ (Λ/J)_X` commutes with shifts. -/
noncomputable instance (J : Ideal Λ) : (reductionModIdeal Λ X J).CommShift ℤ :=
  Functor.CommShift₂.commShiftFlipObj (h := .int) _

/-- The reduction `K ↦ K ⊗ᴸ (Λ/J)_X` is triangulated. -/
instance (J : Ideal Λ) : (reductionModIdeal Λ X J).IsTriangulated :=
  (_root_.DerivedCategory.sheafTensorStructure (Scheme.ProEt.topology X)
    Λ).isTriangulated_tensorRight _

variable {Λ X}

/-- **Reduction modulo `ϖ` detects invertibility of `ϖ`.** For a nonzerodivisor `ϖ` of `Λ` and
`K ∈ D(X_proét, Λ)`, if the reduction `K ⊗ᴸ (Λ/ϖ)_X` vanishes then `ϖ` acts invertibly on `K`:
tensoring the distinguished triangle `Λ ⟶ Λ ⟶ Λ/ϖ ⟶ Λ⟦1⟧` (the first map being the
multiplication by `ϖ`) with `K` gives a distinguished triangle `K ⟶ K ⟶ 0 ⟶ K⟦1⟧` whose first
map is the multiplication by `ϖ`. -/
theorem isIso_smul_id_of_isZero_reductionModIdeal {ϖ : Λ} (hϖ : ϖ ∈ nonZeroDivisors Λ)
    (K : 𝐃(X, Λ)) (hK : IsZero ((reductionModIdeal Λ X (Ideal.span {ϖ})).obj K)) :
    IsIso (ϖ • 𝟙 K) := by
  let T := _root_.DerivedCategory.tensorQuotPowTriangle hϖ rfl K 1
  have hT : T ∈ distTriang _ :=
    _root_.DerivedCategory.tensorQuotPowTriangle_distinguished hϖ rfl K 1
  -- the third vertex of the tensored triangle is the reduction of `K` modulo `ϖ`
  let e : (Ideal.quotPowFunctor (Ideal.span {ϖ})).obj (op 1) ≅
      ModuleCat.of Λ (Λ ⧸ Ideal.span {ϖ}) :=
    (Submodule.quotEquivOfEq _ _ (pow_one _)).toModuleIso
  have h₃ : IsZero T.obj₃ :=
    hK.of_iso (whiskerLeftIso K ((_root_.DerivedCategory.singleFunctor _ 0).mapIso
      ((constantSheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)).mapIso e)))
  have h₁ : IsIso T.mor₁ := (Triangle.isZero₃_iff_isIso₁ _ hT).1 h₃
  have hmor : T.mor₁ = (_root_.DerivedCategory.unitIso K).inv ≫ (ϖ • 𝟙 K) ≫
      (_root_.DerivedCategory.unitIso K).hom := by
    change K ◁ (_root_.DerivedCategory.quotPowTriangle _ hϖ rfl 1).mor₁ = _
    rw [_root_.DerivedCategory.quotPowTriangle_mor₁, pow_one, MonoidalLinear.whiskerLeft_smul,
      MonoidalCategory.whiskerLeft_id, Linear.smul_comp, Category.id_comp, Linear.comp_smul,
      Iso.inv_hom_id]
  have : ϖ • 𝟙 K = (_root_.DerivedCategory.unitIso K).hom ≫ T.mor₁ ≫
      (_root_.DerivedCategory.unitIso K).inv := by
    rw [hmor]; simp
  rw [this]
  infer_instance

/-- **The derived completion inverts morphisms whose reduction is an isomorphism.** A morphism
`u` of `D(X_proét, Λ)` whose reduction modulo a nonzerodivisor `ϖ` is an isomorphism becomes an
isomorphism after derived `ϖ`-completion: its cone `C` has `C ⊗ᴸ (Λ/ϖ)_X = 0`, so `ϖ` acts
invertibly on `C`, and the derived completion inverts such morphisms. -/
theorem isIso_derivedCompletion_map_of_isIso_reductionModIdeal {ϖ : Λ}
    (hϖ : ϖ ∈ nonZeroDivisors Λ) {M N : 𝐃(X, Λ)} (u : M ⟶ N)
    (hu : IsIso ((reductionModIdeal Λ X (Ideal.span {ϖ})).map u)) :
    IsIso ((_root_.DerivedCategory.derivedCompletion (Scheme.ProEt.topology X)
      ⟨ϖ, hϖ, rfl⟩).map u) := by
  obtain ⟨C, g, h, hT⟩ := Pretriangulated.distinguished_cocone_triangle u
  have hC : IsZero ((reductionModIdeal Λ X (Ideal.span {ϖ})).obj C) :=
    (Pretriangulated.Triangle.isZero₃_iff_isIso₁ _
      ((reductionModIdeal Λ X (Ideal.span {ϖ})).map_distinguished _ hT)).2 hu
  exact _root_.DerivedCategory.isIso_derivedCompletion_map_of_smulInvertible _ rfl hT
    (isIso_smul_id_of_isZero_reductionModIdeal hϖ C hC)

end Reduction

/-! ### The completed compact-support exchange map -/

section Exchange

variable {Λ : Type (u + 1)} [CommRing Λ] {I : Ideal Λ}
  (hI : ∃ ϖ ∈ nonZeroDivisors Λ, I = Ideal.span {ϖ})
  {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'} {f : X ⟶ Y} {g : Y' ⟶ Y}

/-- Restriction of scalars `D(X_proét, Λ/Iⁿ) ⥤ D(X_proét, Λ)` along the quotient map. -/
local notation "𝐑𝐞𝐬[" X ", " n "]" =>
  Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) (Ideal.Quotient.mk (I ^ n))

include hI in
/-- Blueprint `lem-fix-operation-reduction`: Basic operations and coefficient reduction; the
compatibility of the reduction `Λ → Λ/Iⁿ` (for `Λ = 𝒪_E` and `I = 𝔪_E`, the reduction
`𝒪_E → A_{E,n}`) with the compact-support exchange transformation.

For an ideal `I` of `Λ` generated by a nonzerodivisor, a cartesian square `g' ≫ f = f' ≫ g`, a
compactification `c` of `f` and `K ∈ D(X_proét, Λ)` with a reduction `K_n = K ⊗ᴸ_Λ Λ/Iⁿ` (a
derived base change `η : K ⟶ Res K_n`, `CategoryTheory.Sheaf.IsDerivedBaseChange`), the
reduction modulo `Iⁿ` of the compact-support exchange map `Ex_!(c) : Lg^* Rf_!(c) K ⟶
Rf'_!(c') Lg'^* K` over `Λ` is isomorphic, as an arrow, to the restriction of scalars of the
exchange map `Ex_!(c)` over `Λ/Iⁿ` at `K_n`.

The blueprint node states that the reduction `𝒪_E → A_{E,n}` commutes with derived pullback and
compact-support direct image, the comparisons preserving the units and counits used to construct
the exchange transformations; the displayed arrow isomorphism is that compatibility for the
compact-support exchange map. -/
theorem nonempty_arrowIso_reductionModIdeal_rightDerivedLowerShriekOfCompactificationBaseChangeMap
    (n : ℕ) (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃(X, Λ))
    (Kn : 𝐃(X, Λ ⧸ I ^ n)) (η : K ⟶ 𝐑𝐞𝐬[X, n].obj Kn) (hη : Sheaf.IsDerivedBaseChange η) :
    Nonempty (Arrow.mk ((reductionModIdeal Λ Y' (I ^ n)).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
          c).app K)) ≅
      Arrow.mk (𝐑𝐞𝐬[Y', n].map ((rightDerivedLowerShriekOfCompactificationBaseChangeMap
        (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) sq c).app Kn))) :=
  sorry

/-- Blueprint `def-cbc-completed-exchange-map`: Completed compact-support exchange map.

For an ideal `I` generated by a nonzerodivisor, a cartesian square `g' ≫ f = f' ≫ g` and a
compactification `c` of `f`, the completed compact-support exchange map
`Ex^comp_!(c) : Lg^*_comp Rf_!(c) ⟶ Rf'_!(c') Lg'^*_comp`, with values in the derived
`I`-complete objects of `D(Y'_proét, Λ)`: the derived completion
`DerivedCategory.derivedCompletion` of the compact-support exchange map `Ex_!(c)`
(`AlgebraicGeometry.ProEtale.rightDerivedLowerShriekOfCompactificationBaseChangeMap`). The
operations on derived complete objects are the derived completions of the plain operations
(the completed pullback `Lg^*_comp K = (Lg^* K)^` of `def-weil-pbc-completed-pullback`), so this
is the composite of the completed exchange maps of the proper part and of the extension by zero
of the blueprint definition. -/
noncomputable def completedRightDerivedLowerShriekOfCompactificationBaseChangeMap
    (sq : IsPullback g' f' f g) (c : Compactification f) :
    Rf_!(c)[ModuleCat.{u + 1} Λ] ⋙ L((g)^*[ModuleCat.{u + 1} Λ]) ⋙
        _root_.DerivedCategory.derivedCompletion (Scheme.ProEt.topology Y') hI ⟶
      L((g')^*[ModuleCat.{u + 1} Λ]) ⋙ Rf_!(c.ofIsPullback sq)[ModuleCat.{u + 1} Λ] ⋙
        _root_.DerivedCategory.derivedCompletion (Scheme.ProEt.topology Y') hI :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (rightDerivedLowerShriekOfCompactificationBaseChangeMap
      (ModuleCat.{u + 1} Λ) sq c) _ ≫ (Functor.associator _ _ _).hom

lemma completedRightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    (sq : IsPullback g' f' f g) (c : Compactification f) (K : 𝐃(X, Λ)) :
    (completedRightDerivedLowerShriekOfCompactificationBaseChangeMap hI sq c).app K =
      (_root_.DerivedCategory.derivedCompletion (Scheme.ProEt.topology Y') hI).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
          c).app K) := by
  simp [completedRightDerivedLowerShriekOfCompactificationBaseChangeMap]

/-- Blueprint `thm-cbc-complete-proetale`: Complete pro-étale compact-support base change.

Let `I` be an ideal of `Λ` generated by a nonzerodivisor, with finite quotients `Λ/Iⁿ` (the adic
coefficient datum of `def-weil-pbc-adic-coefficient-datum`, for a principal ideal), let
`g' ≫ f = f' ≫ g` be a cartesian square with `g` arbitrary and `c` a compactification of `f`
(`def-cbc-compact-support-square`), and let `K ∈ D(X_proét, Λ)` be derived `I`-complete whose
reductions `K_n = K ⊗ᴸ_Λ Λ/Iⁿ` (derived base changes `η_n : K ⟶ Res K_n`) carry étale-origin
witnesses `K_n ≅ ν_X^* L_n` with `L_n ∈ D⁺(X_ét, Λ/Iⁿ)` (`def-weil-pbc-etale-origin-witness`).
Then the completed compact-support exchange map
`Ex^comp_!(K) : Lg^*_comp Rf_! K ⟶ Rf'_! Lg'^*_comp K` of `def-cbc-completed-exchange-map` is an
isomorphism. It is natural in `K`, being a component of a natural transformation.

Only the first reduction `K_1` is used; the completeness of `K` is not needed for this
formulation, in which the completed operations are the derived completions of the plain ones. -/
theorem isIso_completedRightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    [∀ n : ℕ, Finite (Λ ⧸ I ^ n)] (sq : IsPullback g' f' f g) (c : Compactification f)
    (K : 𝐃(X, Λ)) (_hK : _root_.DerivedCategory.derivedComplete (Scheme.ProEt.topology X) I K)
    (Kn : ∀ n : ℕ, 𝐃(X, Λ ⧸ I ^ n)) (η : ∀ n : ℕ, K ⟶ 𝐑𝐞𝐬[X, n].obj (Kn n))
    (hη : ∀ n : ℕ, Sheaf.IsDerivedBaseChange (η n))
    (hKn : ∀ n : ℕ, DerivedCategory.plusEtaleOrigin (ModuleCat.{u + 1} (Λ ⧸ I ^ n)) X (Kn n)) :
    IsIso ((completedRightDerivedLowerShriekOfCompactificationBaseChangeMap hI sq c).app K) := by
  rw [completedRightDerivedLowerShriekOfCompactificationBaseChangeMap_app]
  have h₁ := isIso_rightDerivedLowerShriekOfCompactificationBaseChangeMap_app
    (Λ ⧸ I ^ 1) sq c (Kn 1) (hKn 1)
  obtain ⟨e⟩ :=
    nonempty_arrowIso_reductionModIdeal_rightDerivedLowerShriekOfCompactificationBaseChangeMap
      hI 1 sq c K (Kn 1) (η 1) (hη 1)
  have h : IsIso ((reductionModIdeal Λ Y' (I ^ 1)).map
      ((rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq
        c).app K)) :=
    ((MorphismProperty.isomorphisms _).arrow_mk_iso_iff e).2 (Functor.map_isIso _ _)
  obtain ⟨ϖ, hϖ, rfl⟩ := hI
  rw [pow_one] at h
  exact isIso_derivedCompletion_map_of_isIso_reductionModIdeal hϖ _ h

end Exchange

end AlgebraicGeometry.ProEtale
