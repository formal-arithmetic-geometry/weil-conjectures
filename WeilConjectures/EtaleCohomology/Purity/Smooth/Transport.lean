/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.EtaleCohomology.Purity.Smooth.BrownComparison

/-!
# Smooth purity for all admissible coefficients

Let `f : X ⟶ Y` be smooth of pure relative dimension `d`. Blueprint `sk-thm-purity-transport`
states that for every admissible coefficient ring `Λ` (a finite ring `A` killed by a power of
`ℓ`, `𝒪_E`, `E` or `ℚ̄_ℓ`) the functor `K ↦ f^* K(d)[2d]` on `Dctf(-, Λ)` is right adjoint to
`Rf_!`, and that there is a unique isomorphism of functors `γ_f : f^*(-)(d)[2d] ≅ f^!`
compatible with the counits of the two adjunctions. In this repository the two kinds of
coefficients live in two formalisms:

* **finite coefficients**: the étale derived categories `Dctf(X, Λ)` of
  `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor`, where smooth purity is
  `sk-thm-smooth-purity` (`WeilConjectures.EtaleCohomology.Purity.Smooth.Basic`); the statement
  is `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.exists_existsUnique_smoothPurityNatIso`
  below, and the restricted finite purity isomorphism
  `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.smoothPurityNatIso` is the counit-compatible
  one (`AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.map_smoothPurityNatIso_hom_app_comp`);
* **`ℓ`-adic coefficients** `𝒪_E`, `E`, `ℚ̄_ℓ`: the pro-étale bounded constructible categories
  `Dᵇc(X)⟦Λ⟧` of module objects, where the statement is
  `AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_smoothPurityNatIso`
  (`WeilConjectures.SmoothPurity.Adjunction`), and its compatibility with change of coefficients
  (blueprint `det-sp-purity-coefficient-change`) is
  `AlgebraicGeometry.ProEtale.CondensedRing.smoothPurityNatIso_coefficientChange`
  (`WeilConjectures.SmoothPurity.CoefficientChange`).

This file also records that, in the étale model of the integral stage, `Rf^!` preserves derived
completeness (`AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek`).

## Main statements

- `AlgebraicGeometry.Etale.DerivedCategoryFiniteTor.exists_existsUnique_smoothPurityNatIso`
- `AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek`
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-! ### Finite coefficients -/

section Finite

open Etale.DerivedCategory

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
  [HasTateTwist.IsNormalized Λ] {k : Type u} [Field k] {X Y : Scheme.{u}}
  (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] [QuasiCompact aY]
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]
  {d : ℕ} (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
  [QuasiCompact f]

/-- The restricted finite purity isomorphism `γ_f : Lf^*(-)(d)[2d] ≅ Rf^!` on `Dctf` is
compatible with the counits of the explicit adjunction `Rf_! ⊣ Lf^*(-)(d)[2d]`, transported
along it, and of `Rf_! ⊣ Rf^!`. -/
lemma DerivedCategoryFiniteTor.map_smoothPurityNatIso_hom_app_comp
    (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y) :
    (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f).map
        ((DerivedCategoryFiniteTor.smoothPurityNatIso Λ aY f θ).hom.app K) ≫
      (DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction Λ aY f).counit.app K =
    (DerivedCategoryFiniteTor.twistShiftPullbackAdjunction Λ aY f θ).counit.app K := by
  have h : (DerivedCategoryFiniteTor.twistShiftPullbackAdjunction Λ aY f θ).counit.app K =
      ((DerivedCategoryFiniteTor.twistShiftPullbackAdjunction Λ aY f θ).homEquiv _ _).symm
        (𝟙 _) := by
    simp [Adjunction.homEquiv_counit]
  rw [h, DerivedCategoryFiniteTor.twistShiftPullbackAdjunction,
    Adjunction.homEquiv_ofNatIsoRight_symm_apply, Adjunction.homEquiv_counit, Iso.symm_inv,
    Category.id_comp]

/-- Blueprint `sk-thm-purity-transport`: Smooth purity for all admissible coefficients (finite
coefficients).

Let `f : X ⟶ Y` be smooth separated of pure relative dimension `d` over a separated finite-type
`k`-scheme `Y`, and `Λ` a finite coefficient ring whose exponent is invertible on `X` and `Y`.
There is an orientation `θ : ω_f ≅ Λ_X(d)[2d]` and an adjunction `Rf_! ⊣ Lf^*(-)(d)[2d]` on
`Dctf`, with counit at `K` the smooth trace `Tr^sm_{f,K}` of the purity isomorphism
(`sk-thm-smooth-purity`), such that the restricted purity isomorphism
`γ_f = smoothPurityNatIso θ : Lf^*(-)(d)[2d] ≅ Rf^!` is the *unique* isomorphism of functors
on `Dctf(Y, Λ)` compatible with the counits of `Rf_! ⊣ Lf^*(-)(d)[2d]` and `Rf_! ⊣ Rf^!`
(`det-sp-comparison-brown-explicit`, `det-sp-comparison-brown-unique`). For étale `f` (`d = 0`)
it gives `Rf^! ≅ Lf^*`.

The `ℓ`-adic coefficients `𝒪_E`, `E`, `ℚ̄_ℓ` are treated in the pro-étale formalism:
`AlgebraicGeometry.ProEtale.CondensedRing.existsUnique_smoothPurityNatIso`. The normalization
of the counit by integration on the affine line is that of the finite smooth trace
(`AlgebraicGeometry.Etale.smoothPurityTrace`); the compatibilities with change of
coefficients, base change and composition are separate statements. -/
theorem DerivedCategoryFiniteTor.exists_existsUnique_smoothPurityNatIso [QuasiSeparatedSpace Y] :
    ∃ (θ : dualizingComplex (ModuleCat.{u + 1} Λ) f ≅
        (twistShift Λ X d).obj (constantComplex Λ X))
      (adj : DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f ⊣
        DerivedCategoryFiniteTor.twistShiftPullback Λ aY (d := d) f),
      (∀ K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y, (adj.counit.app K).hom =
        smoothPurityTrace Λ d f ((Etale.smoothPurityNatIso Λ (d := d) f θ).app K.obj)) ∧
      (∃! γ : DerivedCategoryFiniteTor.twistShiftPullback Λ aY (d := d) f ≅
          DerivedCategoryFiniteTor.rightDerivedUpperShriek Λ aY f,
        ∀ K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y,
          (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f).map (γ.hom.app K) ≫
            (DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction Λ aY f).counit.app K =
          adj.counit.app K) ∧
      ∀ K : DerivedCategoryFiniteTor (ModuleCat.{u + 1} Λ) Y,
        (DerivedCategoryFiniteTor.rightDerivedLowerShriek Λ aY f).map
            ((DerivedCategoryFiniteTor.smoothPurityNatIso Λ aY f θ).hom.app K) ≫
          (DerivedCategoryFiniteTor.rightDerivedUpperShriekAdjunction Λ aY f).counit.app K =
        adj.counit.app K := by
  obtain ⟨θ⟩ := nonempty_iso_dualizingComplex_twistShift Λ (d := d) f aY
  exact ⟨θ, _, DerivedCategoryFiniteTor.twistShiftPullbackAdjunction_counit_app Λ aY f θ,
    DerivedCategoryFiniteTor.existsUnique_twistShiftPullbackIso_counit Λ aY f _,
    DerivedCategoryFiniteTor.map_smoothPurityNatIso_hom_app_comp Λ aY f θ⟩

end Finite

/-! ### Derived completeness at the integral stage -/

section Integral

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E] {X Y : Scheme.{u}} {d : ℕ} (f : X ⟶ Y) [IsSeparated f]
  [SmoothOfRelativeDimension d f] [HasCompactification f]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance localInstance_Transport_1 (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

omit [IsSeparated f] in
/-- **`Rf^!` preserves derived completeness.** Let `f : X ⟶ Y` be smooth separated of pure
relative dimension `d` and let `Λ = 𝒪_E` be the integral coefficient stage in the étale model
`D(Y_ét, 𝒪_E)`. Then `Rf^!` carries derived-complete objects of `D(Y_ét, 𝒪_E)` to
derived-complete objects of `D(X_ét, 𝒪_E)`, so that it restricts to the adic categories
`D_comp(−, 𝒪_E)`. The exceptional inverse image `Rf^!` at the integral stage is the right adjoint
of `Rf_!`, whose existence is assumed here: the instance
`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` only covers finite coefficients.

Derived complete objects are those receiving no nonzero map from an object on which a
uniformizer `ϖ` of `𝒪_E` acts invertibly
(`DerivedCategory.derivedComplete_iff_rightOrthogonal`). A map `L ⟶ Rf^! K` is adjoint to a
map `Rf_! L ⟶ K`, and `ϖ` acts invertibly on `Rf_! L` if it does on `L`, since `Rf_!` is
`𝒪_E`-linear. -/
theorem derivedCompleteIntegral_rightDerivedUpperShriek
    [(R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).IsLeftAdjoint]
    (K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology
      (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E)))))
    (hK : DerivedCategory.derivedCompleteIntegral Y.smallEtaleTopology l E K) :
    DerivedCategory.derivedCompleteIntegral X.smallEtaleTopology l E
      ((rightDerivedUpperShriek
        (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) f).obj K) := by
  obtain ⟨ϖ, hϖ, hI⟩ :=
    PadicAlgCl.exists_mem_nonZeroDivisors_maximalIdealShrink_eq_span.{w, u} l E
  rw [DerivedCategory.derivedCompleteIntegral,
    DerivedCategory.derivedComplete_iff_rightOrthogonal hϖ hI] at hK ⊢
  intro L φ (hL : IsIso (ϖ • 𝟙 L))
  let adj := rightDerivedUpperShriekAdjunction
    (ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))) f
  have hL' : DerivedCategory.smulInvertible Y.smallEtaleTopology ϖ
      ((R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).obj L) := by
    change IsIso (ϖ • 𝟙 _)
    rw [← (R(f)_![ModuleCat.{u + 1} (Shrink.{u + 1} (PadicAlgCl.integers l E))]).map_id,
      ← Functor.map_smul]
    infer_instance
  rw [← (adj.homEquiv L K).apply_symm_apply φ, hK ((adj.homEquiv L K).symm φ) hL',
    Adjunction.homEquiv_unit,
    Functor.map_zero, comp_zero]

end Integral

end Etale

end AlgebraicGeometry
