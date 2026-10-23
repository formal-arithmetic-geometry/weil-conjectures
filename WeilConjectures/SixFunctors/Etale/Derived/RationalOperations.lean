/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.RationalizationRecollement
public import WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral
public import WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients

/-!
# The rational internal hom and exceptional inverse image

Let `E/ℚ_ℓ` be finite inside `ℚ̄_ℓ` with ring of integers `𝒪_E`. As in
`WeilConjectures.SixFunctors.Etale.Derived.CompactSupportIntegral`, the integral stage is the
category `D_comp(X_ét, 𝒪_E)` of derived complete objects
(`DerivedCategoryDerivedCompleteIntegral`) and the rational stage its rationalization
`D_comp(X_ét, E)` (`DerivedCategoryDerivedCompleteRational`); the rational operations are the
ones *defined by coefficient passage*: the functors induced on rationalizations by `𝒪_E`-linear
triangulated integral functors (`CategoryTheory.Rationalization.map`).

This file proves the parts of blueprint `lem-coef-rational-operations` that this model can
express:

- **the exceptional adjunction.** The integral `Rf^!` preserves derived completeness
  (`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek`), and on
  `D_comp(-, 𝒪_E)` it is right adjoint to the integral compact support `(Rf_! -)^`
  (`AlgebraicGeometry.Etale.rightDerivedLowerShriekUpperShriekDerivedCompleteIntegralAdjunction`).
  Localizing this adjunction gives the adjunction `Rf_{!,E} ⊣ Rf_E^!` at `E`, whose unit and
  counit are the rationalizations of the integral ones
  (`AlgebraicGeometry.Etale.rightDerivedLowerShriekUpperShriekDerivedCompleteRationalAdjunction`),
  and the rational dualizing object `ω_{X,E} = Ra_{X,E}^! E`
  (`AlgebraicGeometry.Etale.dualizingComplexDerivedCompleteRational`).
- **the completion adjunction and the internal hom.** For a derived complete `K`, the
  completed tensor product `P ↦ (K ⊗ᴸ P)^` is left adjoint to `RHom_{𝒪_E}(K, -)` on
  `D_comp(-, 𝒪_E)` (`AlgebraicGeometry.Etale.completedTensorDerivedHomAdjunction`), the
  ambient tensor–hom adjunction followed by the completion adjunction. Localizing it identifies
  the rational internal hom `RHom_E(K, -)` (coefficient passage) as the right adjoint of the
  rational completed tensor product, with the localized evaluation as counit
  (`AlgebraicGeometry.Etale.completedTensorDerivedHomRationalAdjunction`), and the rational
  Verdier dual is `D_{X,E} K = RHom_E(K, ω_{X,E})`
  (`AlgebraicGeometry.Etale.verdierDualDerivedCompleteRational`).

## What is not stated

- The formula `Rf_E^! ≅ D_{X,E} f^* D_{Y,E}` and the duality theory of `D_{X,E}` (biduality,
  `thm-coef-rational-verdier`) are not in the repository: the integral formula
  `G_f L ≅ 𝔻_X f^*_comp 𝔻_Y L` of `prop-coef-integral-exceptional-adjoint`
  (`AlgebraicGeometry.Etale.boundedConstructibleIntegral_exceptionalAdjoint`) is only an
  objectwise `Nonempty` isomorphism, which does not localize, and there is no integral or
  rational Verdier dual functor.
- The compatibility with finite scalar extension `E ⊆ E'` (`lem-coef-integral-finite-extension`)
  is not stated.
- The operations are defined on all of `D_comp(-, E)`; their preservation of the constructible
  subcategories is `prop-coef-integral-exceptional-adjoint` and `cor-coef-integral-internal-hom`.
-/

@[expose] public section

universe w u

open CategoryTheory Limits Pretriangulated Opposite

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

set_option hygiene false in
/-- The coefficient category `ModuleCat 𝒪_E` of the integral stage. -/
local notation "𝐌" => ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))

set_option hygiene false in
/-- The derived category `D(X_ét, 𝒪_E)`. -/
local notation "𝐃(" X ")" => _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) 𝐌)

section Exceptional

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [HasCompactification f] [(R(f)_![𝐌]).IsLeftAdjoint]

local instance : (rightDerivedUpperShriekAdjunction 𝐌 f).CommShift ℤ :=
  (rightDerivedUpperShriekAdjunction 𝐌 f).commShift_of_leftAdjoint ℤ

local instance : (R(f)^![𝐌]).IsTriangulated :=
  (rightDerivedUpperShriekAdjunction 𝐌 f).isTriangulated_rightAdjoint

local instance : (R(f)^![𝐌]).Linear (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  (rightDerivedUpperShriekAdjunction 𝐌 f).right_adjoint_linear

/-- The exceptional inverse image `Rf^!` preserves derived completeness at the integral stage:
it is right adjoint to the `𝒪_E`-linear `Rf_!`, which preserves the objects on which a
uniformizer acts invertibly, and the derived complete objects are those right orthogonal to
these. -/
theorem derivedCompleteIntegral_rightDerivedUpperShriek (L : 𝐃(Y))
    (hL : DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E L) :
    DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E ((R(f)^![𝐌]).obj L) := by
  obtain ⟨ϖ, hϖ, hI⟩ := PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  change _root_.DerivedCategory.derivedComplete _ (PadicAlgCl.maximalIdealShrink l E) _ at hL ⊢
  rw [_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ hI] at hL ⊢
  intro Z g (hZ : IsIso (ϖ • 𝟙 Z))
  let adj := rightDerivedUpperShriekAdjunction 𝐌 f
  have hZ' : _root_.DerivedCategory.smulInvertible Y.smallEtaleTopology ϖ
      ((R(f)_![𝐌]).obj Z) := by
    change IsIso (ϖ • 𝟙 _)
    rw [← (R(f)_![𝐌]).map_id, ← Functor.map_smul]
    infer_instance
  rw [← (adj.homEquiv Z L).apply_symm_apply g, hL ((adj.homEquiv Z L).symm g) hZ',
    Adjunction.homEquiv_unit, Functor.map_zero, Limits.comp_zero]

/-- `Rf^!` on derived complete objects, as a functor between the full subcategories. -/
noncomputable abbrev rightDerivedUpperShriekDerivedCompleteIntegralAux :
    (DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).FullSubcategory ⥤
      (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).FullSubcategory :=
  (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).lift
    ((DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E).ι ⋙ R(f)^![𝐌])
    (fun L ↦ derivedCompleteIntegral_rightDerivedUpperShriek l E f _ L.property)

/-- Blueprint `prop-coef-integral-exceptional-adjoint` (the functor): the integral exceptional
inverse image `Rf^! : D_comp(Y_ét, 𝒪_E) ⥤ D_comp(X_ét, 𝒪_E)`, the restriction of `Rf^!`
(`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek`). -/
noncomputable def rightDerivedUpperShriekDerivedCompleteIntegral :
    DerivedCategoryDerivedCompleteIntegral Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E :=
  rightDerivedUpperShriekDerivedCompleteIntegralAux l E f

noncomputable instance : (rightDerivedUpperShriekDerivedCompleteIntegral l E f).CommShift ℤ :=
  inferInstanceAs ((rightDerivedUpperShriekDerivedCompleteIntegralAux l E f).CommShift ℤ)

instance : (rightDerivedUpperShriekDerivedCompleteIntegral l E f).IsTriangulated :=
  inferInstanceAs (rightDerivedUpperShriekDerivedCompleteIntegralAux l E f).IsTriangulated

instance : (rightDerivedUpperShriekDerivedCompleteIntegral l E f).Linear
    (Shrink.{u + 1} (PadicAlgCl.integers l E)) where
  map_smul _ _ :=
    (DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E).ι.map_injective <|
      (R(f)^![𝐌]).map_smul _ _

/-- Blueprint `prop-coef-integral-exceptional-adjoint` (the adjunction): on derived complete
objects, the integral exceptional inverse image is right adjoint to the integral compact support
`K ↦ (Rf_! K)^` (`AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedCompleteIntegral`). It is
the adjunction `Rf_! ⊣ Rf^!` composed with the completion adjunction `(-)^ ⊣ ι`, restricted to
`D_comp(X_ét, 𝒪_E)`: `Hom((Rf_! K)^, L) = Hom(Rf_! K, L) = Hom(K, Rf^! L)` for `L` complete. -/
noncomputable def rightDerivedLowerShriekUpperShriekDerivedCompleteIntegralAdjunction :
    rightDerivedLowerShriekDerivedCompleteIntegral l E f ⊣
      rightDerivedUpperShriekDerivedCompleteIntegral l E f :=
  ((rightDerivedUpperShriekAdjunction 𝐌 f).comp
      (DerivedCategoryDerivedCompleteIntegral.completionAdjunction _ l E)).restrictFullyFaithful
    (ObjectProperty.fullyFaithfulι _) (Functor.FullyFaithful.id _)
    (Functor.rightUnitor _).symm
    (Functor.leftUnitor _ ≪≫ (ObjectProperty.liftCompιIso _ _ _).symm)

/-- Blueprint `lem-coef-rational-operations` (the exceptional inverse image): the rational
exceptional inverse image `Rf_E^! : D_comp(Y_ét, E) ⥤ D_comp(X_ét, E)`, induced on the
rationalizations by the `𝒪_E`-linear triangulated integral `Rf^!` (coefficient passage). -/
noncomputable def rightDerivedUpperShriekDerivedCompleteRational :
    DerivedCategoryDerivedCompleteRational Y.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteRational X.smallEtaleTopology l E :=
  Rationalization.map _ (rightDerivedUpperShriekDerivedCompleteIntegral l E f)

/-- Blueprint `lem-coef-rational-operations` (the exceptional adjunction): `Rf_E^!` is right
adjoint to the rational compact support `Rf_{!,E}`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekDerivedCompleteRational`, blueprint
`def-weil-integral-rational-qbar-compact-support`). The adjunction is the localization of the
integral exceptional adjunction
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekUpperShriekDerivedCompleteIntegralAdjunction`,
`prop-coef-integral-exceptional-adjoint`), so its unit and counit are the rationalizations of the
integral ones
(`CategoryTheory.Rationalization.mapAdjunction_unit_app`,
`CategoryTheory.Rationalization.mapAdjunction_counit_app`). -/
noncomputable def rightDerivedLowerShriekUpperShriekDerivedCompleteRationalAdjunction :
    rightDerivedLowerShriekDerivedCompleteRational l E f ⊣
      rightDerivedUpperShriekDerivedCompleteRational l E f :=
  Rationalization.mapAdjunction _
    (rightDerivedLowerShriekUpperShriekDerivedCompleteIntegralAdjunction l E f)

end Exceptional

section InternalHom

variable {X : Scheme.{u}} (K : 𝐃(X))

local instance : ((derivedHom 𝐌 X).obj (op K)).CommShift ℤ :=
  (derivedTensorHomAdjunction 𝐌 K).rightAdjointCommShift ℤ

local instance : (derivedTensorHomAdjunction 𝐌 K).CommShift ℤ :=
  (derivedTensorHomAdjunction 𝐌 K).commShift_of_leftAdjoint ℤ

local instance : ((derivedHom 𝐌 X).obj (op K)).IsTriangulated :=
  (derivedTensorHomAdjunction 𝐌 K).isTriangulated_rightAdjoint

local instance : ((derivedHom 𝐌 X).obj (op K)).Linear
    (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  (derivedTensorHomAdjunction 𝐌 K).right_adjoint_linear

/-- The completed tensor product `P ↦ (K ⊗ᴸ P)^` of `D_comp(X_ét, 𝒪_E)`: the derived tensor
product followed by the derived completion (`R lim_n (K ⊗ᴸ P) ⊗ᴸ 𝒪_E/𝔪_Eⁿ`, the blueprint's
`K ⊗̂ᴸ P`). -/
noncomputable def completedTensorDerivedCompleteIntegral :
    DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E ⥤
      DerivedCategoryDerivedCompleteIntegral X.smallEtaleTopology l E :=
  DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙ (derivedTensor 𝐌 X).obj K ⋙
    DerivedCategoryDerivedCompleteIntegral.completion _ l E

noncomputable instance : (completedTensorDerivedCompleteIntegral l E K).CommShift ℤ :=
  inferInstanceAs ((DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙
    (derivedTensor 𝐌 X).obj K ⋙ DerivedCategoryDerivedCompleteIntegral.completion _ l E).CommShift
      ℤ)

instance : (completedTensorDerivedCompleteIntegral l E K).IsTriangulated :=
  inferInstanceAs ((DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙
    (derivedTensor 𝐌 X).obj K ⋙
      DerivedCategoryDerivedCompleteIntegral.completion _ l E).IsTriangulated)

instance : (completedTensorDerivedCompleteIntegral l E K).Linear
    (Shrink.{u + 1} (PadicAlgCl.integers l E)) :=
  inferInstanceAs ((DerivedCategoryDerivedCompleteIntegral.ι _ l E ⋙
    (derivedTensor 𝐌 X).obj K ⋙ DerivedCategoryDerivedCompleteIntegral.completion _ l E).Linear _)

end InternalHom

end Etale

end AlgebraicGeometry
