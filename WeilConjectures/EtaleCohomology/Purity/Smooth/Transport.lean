/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalCoefficient
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic

/-!
# Smooth purity over `𝒪_E`, `E` and `ℚ̄_ℓ`

Smooth purity is proved at the finite coefficient stage in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Basic`. This file records what the three
remaining coefficient stages of the `ℓ`-adic formalism need: the adic category over `𝒪_E`, its
rationalization over `E`, and the colimit over finite extensions `E/ℚ_ℓ` giving `ℚ̄_ℓ`.

In this repository the `𝒪_E` stage is the derived-complete subcategory
`AlgebraicGeometry.DerivedCategory.derivedCompleteIntegral` of the derived category of sheaves
of `𝒪_E`-modules, and the `E` stage is its rationalization
`AlgebraicGeometry.DerivedCategoryDerivedCompleteRational`.

## Implementation notes

The one statement here is the genuinely new content of `sk-thm-purity-transport`: that `Rf^!`
preserves derived completeness, which is what makes the `𝒪_E` stage a stage at all.

Everything else in that subsection is either formal or unavailable. The purity isomorphism on
derived-complete objects is `sk-thm-smooth-purity` read at `Λ = 𝒪_E`, since derived
completeness is a property of objects of the ambient derived category and the purity
isomorphism is an isomorphism there. The `E` statement is its image under the localization
functor `DerivedCategoryDerivedCompleteRational.fromIntegral`, and the `ℚ̄_ℓ` statement its
colimit over finite `E/ℚ_ℓ` — a colimit category the repository does not yet have. What is
*not* formal, and is not stated because the finite reductions `𝒪_E → A_{E,n}` are not
available as functors here, is that `γ_{f,K}` extends the finite-coefficient isomorphism
compatibly with those reductions.

## Main statements

- `AlgebraicGeometry.Etale.derivedCompleteIntegral_rightDerivedUpperShriek`

## Proof

Derived complete objects are those receiving no nonzero map from an object on which a
uniformizer `ϖ` of `𝒪_E` acts invertibly
(`DerivedCategory.derivedComplete_iff_rightOrthogonal`). A map `L ⟶ Rf^! K` is adjoint to a
map `Rf_! L ⟶ K`, and `ϖ` acts invertibly on `Rf_! L` if it does on `L`, since `Rf_!` is
`𝒪_E`-linear.
-/

@[expose] public section

universe w u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (l : ℕ) [Fact l.Prime] (E : Type w) [Field E] [Algebra E (PadicAlgCl l)]
  [Algebra ℚ_[l] E] [IsScalarTower ℚ_[l] E (PadicAlgCl l)] [FiniteDimensional ℚ_[l] E]
  [Small.{u + 1} E] {X Y : Scheme.{u}} {d : ℕ} (f : X ⟶ Y) [IsSeparated f]
  [SmoothOfRelativeDimension d f] [HasCompactification f]

/-- The small étale site of a scheme is essentially small. Instance search does not find this
in the presence of the imports of this file. -/
local instance (X : Scheme.{u}) : EssentiallySmall.{u + 1} X.Etale :=
  have : LocallySmall.{u + 1} X.Etale :=
    @locallySmall_of_univLE X.Etale _ (@univLE_of_max.{u, u + 1} UnivLE.self)
  essentiallySmall_of_small_of_locallySmall _

omit [IsSeparated f] in
/-- Blueprint `sk-thm-purity-transport`: Smooth purity over `𝒪_E`, `E` and `ℚ̄_ℓ`

**`Rf^!` preserves derived completeness.** Let `f : X ⟶ Y` be smooth separated of pure
relative dimension `d` and let `Λ = 𝒪_E` be the integral coefficient stage. Then `Rf^!`
carries derived-complete objects of `D(Y_ét, 𝒪_E)` to derived-complete objects of
`D(X_ét, 𝒪_E)`, so that it restricts to the adic categories `D_comp(−, 𝒪_E)` in which the
`ℓ`-adic formalism is typed. The exceptional inverse image `Rf^!` at the integral stage is the
right adjoint of `Rf_!`, whose existence is assumed here: the instance
`AlgebraicGeometry.Etale.isLeftAdjoint_rightDerivedLowerShriek` only covers finite coefficients.

Given this, the purity isomorphism `γ_{f,K} : (Lf^* K)(d)[2d] ≅ Rf^! K` at the adic stage is
`sk-thm-smooth-purity` read at `Λ = 𝒪_E`, and applying
`AlgebraicGeometry.DerivedCategoryDerivedCompleteRational.fromIntegral` gives it over `E`. -/
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

end Etale

end AlgebraicGeometry
