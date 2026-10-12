/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.IntegralCoefficient
public import WeilConjectures.SixFunctors.Etale.Derived.Invertible
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.Etale.Derived.Perfect

/-!
# Derived completeness and the six operations

Let `Λ` be a domain and `I` a principal ideal of `Λ`, so that every `Λ/Iⁿ` is a perfect
`Λ`-module. This file records that the operations used by Poincaré duality carry objects of
`D(X_ét, Λ)` that are derived complete for `I` (`DerivedCategory.derivedComplete`) to derived
complete objects. At the integral stage `Λ = 𝒪_E`, `I = 𝔪_E` of the `ℓ`-adic formalism these
say that the operations restrict to the adic categories `D_comp(−, 𝒪_E)` of
`DerivedCategory.derivedCompleteIntegral`. Together with
`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek` (in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`), for `Rf^!`, this places every
object of the derived Poincaré pairing at `Λ = 𝒪_E` in the adic category.

## Main statements

- `AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerStar`: `Rf_*` preserves derived
  completeness.
- `AlgebraicGeometry.Etale.derivedComplete_rightDerivedLowerShriek`: so does `Rf_!`.
- `AlgebraicGeometry.Etale.derivedComplete_coefficientDual`: so does the coefficient dual
  `K ↦ K^∨`, provided the constant complex `Λ_X` is itself derived complete.

The `derivedCompleteIntegral_*` versions are their specialisations to `𝒪_E`.

## Implementation notes

The hypotheses on `(Λ, I)` are only used to make each `Λ/Iⁿ` perfect, through
`AlgebraicGeometry.Etale.nonempty_iso_reductionModIdeal_rightDerivedLowerStar`. For `𝒪_E` the
ideal `𝔪_E` is principal when `E` is finite over `ℚ_ℓ`
(`PadicAlgCl.isPrincipal_maximalIdealShrink`), which is why the specialisations assume it.

The blueprint states `sk-thm-transport` at the three stages `𝒪_E`, `E` and `ℚ̄_ℓ`. Only the
integral stage `𝒪_E` is stated here, and only its non-formal part: that the operations preserve
derived completeness. The `E` stage would be the image of these statements under the
rationalization `DerivedCategoryDerivedCompleteRational.fromIntegral`, and the `ℚ̄_ℓ` stage
their colimit over finite extensions `E/ℚ_ℓ`, a colimit category the repository does not have;
neither is stated. Which coefficient category carries the `E` and `ℚ̄_ℓ` stages is not decided
here.
-/

@[expose] public section

universe w u

open CategoryTheory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

set_option hygiene false in
/-- The constant complex `Λ_X`: the constant sheaf `Λ` on `X_ét`, placed in degree `0`. It is
the monoidal unit of `D(X_ét, Λ)` up to `DerivedCategory.εSingleFunctorZero`; it is spelled this
way so that the monoidal structure of the derived category stays out of the statements below
(see the implementation notes of `WeilConjectures.CategoryTheory.DerivedCategory.Complete.Defs`).
-/
local notation "Λ_(" X ", " Λ ")" =>
  (_root_.DerivedCategory.singleFunctor (Sheaf (Scheme.smallEtaleTopology X)
    (ModuleCat.{u + 1} Λ)) 0).obj
      ((constantSheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ)).obj (ModuleCat.of Λ Λ))

/-- `Rf_*` preserves the right orthogonal of the objects on which `ϖ` acts invertibly: a map
`Z ⟶ Rf_* K` is the transpose of a map `Lf^* Z ⟶ K`, and `ϖ` acts invertibly on `Lf^* Z`, the
derived pullback being `Λ`-linear. -/
lemma rightOrthogonal_smulInvertible_rightDerivedLowerStar {Λ : Type (u + 1)} [CommRing Λ]
    (ϖ : Λ) {X Y : Scheme.{u}} (f : X ⟶ Y) (K : 𝐃(X, Λ))
    (hK : (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal K) :
    (_root_.DerivedCategory.smulInvertible Y.smallEtaleTopology ϖ).rightOrthogonal
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  intro Z g (hZ : IsIso (ϖ • 𝟙 Z))
  let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f
  have hZ' : IsIso (ϖ • 𝟙 ((L((f)^*[ModuleCat.{u + 1} Λ])).obj Z)) := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance
  have h := hK ((adj.homEquiv _ _).symm g) hZ'
  rw [← (adj.homEquiv _ _).apply_symm_apply g, h, Adjunction.homEquiv_unit,
    Functor.map_zero, Limits.comp_zero]

/-- The coefficient dual `RHom(K, Λ_X)` lies in the right orthogonal of the objects on which `ϖ`
acts invertibly as soon as `Λ_X` does: a map `Z ⟶ RHom(K, Λ_X)` is the transpose of a map
`K ⊗ᴸ Z ⟶ Λ_X`, and `ϖ` acts invertibly on `K ⊗ᴸ Z`, the derived tensor product being
`Λ`-linear. -/
lemma rightOrthogonal_smulInvertible_coefficientDual {Λ : Type (u + 1)} [CommRing Λ]
    (ϖ : Λ) {X : Scheme.{u}}
    (hΛ : (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal
      Λ_(X, Λ)) (K : 𝐃(X, Λ)) :
    (_root_.DerivedCategory.smulInvertible X.smallEtaleTopology ϖ).rightOrthogonal
      ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K)) := by
  intro Z g (hZ : IsIso (ϖ • 𝟙 Z))
  let e := singleFunctorObjUnitIso (ModuleCat.{u + 1} Λ) X
  let adj := derivedTensorHomAdjunction (ModuleCat.{u + 1} Λ) (X := X) K
  have hZ' : IsIso (ϖ • 𝟙 (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).obj Z)) := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_smul]
    infer_instance
  have h : (adj.homEquiv _ _).symm g = 0 := by
    have := hΛ ((adj.homEquiv _ _).symm g ≫ e.inv) hZ'
    rw [← Category.comp_id ((adj.homEquiv _ _).symm g), ← e.inv_hom_id, ← Category.assoc,
      this, Limits.zero_comp]
  rw [← (adj.homEquiv _ _).apply_symm_apply g, h, Adjunction.homEquiv_unit,
    Functor.map_zero, Limits.comp_zero]

section General

variable {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ] (I : Ideal Λ) (hI : I.IsPrincipal)

include hI

/-- **`Rf_*` preserves derived completeness.** For a principal ideal `I` of a domain `Λ` and
every morphism `f : X ⟶ Y`, the derived direct image `Rf_*` carries objects of `D(X_ét, Λ)`
that are derived complete for `I` to derived complete objects of `D(Y_ét, Λ)`. -/
theorem derivedComplete_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y) (K : 𝐃(X, Λ))
    (hK : DerivedCategory.derivedComplete X.smallEtaleTopology I K) :
    DerivedCategory.derivedComplete Y.smallEtaleTopology I
      ((R((f)_*[ModuleCat.{u + 1} Λ])).obj K) := by
  -- For `I = 0` every object is derived complete. For `I = (ϖ)` with `ϖ ≠ 0`, derived
  -- completeness is right orthogonality to the objects on which `ϖ` acts invertibly
  -- (`derivedComplete_iff_rightOrthogonal`), and `Rf_*` preserves it by adjunction.
  obtain ⟨ϖ, hϖI⟩ := hI.principal
  by_cases h0 : ϖ = 0
  · -- `I = 0`: every object is derived complete
    obtain rfl : I = ⊥ := by rw [hϖI, h0, Ideal.span_singleton_eq_bot]
    exact _root_.DerivedCategory.derivedComplete_bot _
  have hϖ : ϖ ∈ nonZeroDivisors Λ := mem_nonZeroDivisors_of_ne_zero h0
  rw [_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ hϖI] at hK ⊢
  exact rightOrthogonal_smulInvertible_rightDerivedLowerStar ϖ f K hK

/-- **`Rf_!` preserves derived completeness.** For a principal ideal `I` of a domain `Λ` and
`f : X ⟶ Y` admitting a compactification, `Rf_!` carries objects of `D(X_ét, Λ)` that are
derived complete for `I` to derived complete objects of `D(Y_ét, Λ)`. For `Y = Spec k` this
says that `RΓ_c(X, K)` is derived complete. -/
theorem derivedComplete_rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : 𝐃(X, Λ))
    (hK : DerivedCategory.derivedComplete X.smallEtaleTopology I K) :
    DerivedCategory.derivedComplete Y.smallEtaleTopology I
      ((R(f)_![ModuleCat.{u + 1} Λ]).obj K) :=
  -- Proof sketch: for the chosen compactification `f = g ∘ j`, with `j` an open immersion and
  -- `g` proper, `Rf_! = Rg_* j_!`, and `Rg_*` preserves derived completeness by
  -- `derivedComplete_rightDerivedLowerStar`. It remains to see that `j_! K` is derived
  -- complete. This is the non-formal step and it is open here: `j_!` is a left adjoint, so it
  -- commutes with `– ⊗ᴸ Λ/Iⁿ` (projection formula for `j`) but need not preserve the
  -- products in the Milnor triangle of `K`. A possible route is the triangle
  -- `j_! K → Rj_* K → i_* i^* Rj_* K` for the closed complement `i`: `Rj_* K` and `i_*` of a
  -- complete object are complete by the argument for `Rf_*`, so it suffices that `i^*`
  -- preserves completeness of `Rj_* K`. Should that fail, `Rf_!` on the adic category has to
  -- be defined as the derived completion of `Rg_* j_!`.
  sorry

/-- **The coefficient dual preserves derived completeness.** For a principal ideal `I` of a
domain `Λ` and a scheme `X` on which the constant complex `Λ_X` is derived complete for
`I`, the coefficient dual `K^∨ = RHom(K, Λ_X)` of an object `K` of `D(X_ét, Λ)` that is derived
complete for `I` is derived complete.

The hypothesis on `Λ_X` is not automatic: if `π₀(X)` is an infinite profinite space, the global
sections of `Λ_X` are the locally constant functions `π₀(X) → Λ`, whereas those of
`lim_n (Λ/Iⁿ)_X` are the continuous ones. -/
theorem derivedComplete_coefficientDual {X : Scheme.{u}}
    (hΛ : DerivedCategory.derivedComplete X.smallEtaleTopology I Λ_(X, Λ)) (K : 𝐃(X, Λ))
    (hK : DerivedCategory.derivedComplete X.smallEtaleTopology I K) :
    DerivedCategory.derivedComplete X.smallEtaleTopology I
      ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) X).obj (op K)) := by
  -- For `I = 0` every object is derived complete. For `I = (ϖ)` with `ϖ ≠ 0`, derived
  -- completeness is right orthogonality to the objects on which `ϖ` acts invertibly, which
  -- passes from `Λ_X` to `RHom(K, Λ_X)` by adjunction. The hypothesis `hK` is not needed.
  obtain ⟨ϖ, hϖI⟩ := hI.principal
  by_cases h0 : ϖ = 0
  · obtain rfl : I = ⊥ := by rw [hϖI, h0, Ideal.span_singleton_eq_bot]
    exact _root_.DerivedCategory.derivedComplete_bot _
  have hϖ : ϖ ∈ nonZeroDivisors Λ := mem_nonZeroDivisors_of_ne_zero h0
  rw [_root_.DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ hϖI] at hΛ ⊢
  exact rightOrthogonal_smulInvertible_coefficientDual ϖ hΛ K

end General

section Integral

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Small.{u + 1} E] [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)]
  [FiniteDimensional ℚ_[l] E]

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**`Rf_*` preserves derived completeness at the integral stage.** For `E` finite over `ℚ_ℓ` and
every morphism `f : X ⟶ Y`, `Rf_*` carries derived-complete objects of `D(X_ét, 𝒪_E)` to
derived-complete objects of `D(Y_ét, 𝒪_E)`. -/
theorem derivedCompleteIntegral_rightDerivedLowerStar {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : 𝐃(X, Shrink.{u + 1} (PadicAlgCl.integers l E)))
    (hK : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R((f)_*[ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))])).obj K) :=
  derivedComplete_rightDerivedLowerStar _ (PadicAlgCl.isPrincipal_maximalIdealShrink l E) f K hK

/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**`Rf_!` preserves derived completeness at the integral stage.** For `E` finite over `ℚ_ℓ` and
`f : X ⟶ Y` admitting a compactification, `Rf_!` carries derived-complete objects of
`D(X_ét, 𝒪_E)` to derived-complete objects of `D(Y_ét, 𝒪_E)`. For `Y = Spec k` this says that
`RΓ_c(X, K)` is an object of the adic category `D_comp(Spec k, 𝒪_E)`. -/
theorem derivedCompleteIntegral_rightDerivedLowerShriek {X Y : Scheme.{u}} (f : X ⟶ Y)
    [HasCompactification f] (K : 𝐃(X, Shrink.{u + 1} (PadicAlgCl.integers l E)))
    (hK : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E
      ((R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).obj K) :=
  derivedComplete_rightDerivedLowerShriek _ (PadicAlgCl.isPrincipal_maximalIdealShrink l E) f K
    hK

attribute [-instance] Shrink.instRing in
/-- Blueprint `sk-thm-transport`: Transport through the coefficient stages.

**The dual at the integral stage.** For `E` finite over `ℚ_ℓ` and a scheme `X` on which the
constant complex `𝒪_E` is derived complete, the coefficient dual `K^∨ = RHom(K, 𝒪_E)` of a
derived-complete object of `D(X_ét, 𝒪_E)` is derived complete. -/
theorem derivedCompleteIntegral_coefficientDual {X : Scheme.{u}}
    (hΛ : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      Λ_(X, Shrink.{u + 1} (PadicAlgCl.integers l E)))
    (K : 𝐃(X, Shrink.{u + 1} (PadicAlgCl.integers l E)))
    (hK : DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      ((DerivedCategory.coefficientDual
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) X).obj (op K)) :=
  derivedComplete_coefficientDual _ (PadicAlgCl.isPrincipal_maximalIdealShrink l E) hΛ K hK

end Integral

end Etale

end AlgebraicGeometry
