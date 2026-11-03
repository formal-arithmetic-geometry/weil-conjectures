/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.QuasiCompact
public import WeilConjectures.EtaleCohomology.Purity.Smooth.SectionThomFrames

/-!
# Smooth purity by the diagonal argument

For `f : X ⟶ Y` smooth separated of pure relative dimension `d` and a finite coefficient ring
`Λ` whose exponent is invertible on `X`, the dualizing complex of the projections of
`X ×_Y X` is the pullback of `ω_f`, the section invariant of the diagonal is `ω_f`, and
`ω_f ≅ Λ_X(d)[2d]` (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`). The
smooth purity map and its compatibility with base change are in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Basic`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {d : ℕ} (f : X ⟶ Y) [IsSeparated f] [SmoothOfRelativeDimension d f] [HasCompactification f]
  [HasInvertibleExponent Λ X]

/-! ### The diagonal -/

omit [HasTateTwist Λ] [IsSeparated f] in
include d in
/-- Blueprint `lem-pur-diagonal-base-change`: Base change for the dualizing object of a
projection

Let `W = X ×_Y X` with projections `p₁, p₂`. The square `p₂ ≫ f = p₁ ≫ f` is cartesian and
`p₁` is the base change of the smooth `f`, so smooth base change for `R^!` (`sk-prop-cohsm`
(c)) gives

`ω_{p₁} = Rp₁^! Λ_X ≅ Lp₂^* Rf^! Λ_Y = Lp₂^* ω_f`.

Smooth base change is available over a quasi-separated base `Y` for the quasi-compact base
change `p₁` of `f`; both hold for `f` and `Y` of finite type over a field, as in the blueprint. -/
theorem nonempty_iso_dualizingComplex_pullbackFst [QuasiSeparatedSpace Y] [QuasiCompact f] :
    Nonempty (dualizingComplex Λ (pullback.fst f f) ≅
      (L((pullback.snd f f)^*[ModuleCat.{u + 1} Λ])).obj
        (dualizingComplex Λ f)) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek Λ (d := d) f
    (IsPullback.of_hasPullback f f).flip
  obtain ⟨ι⟩ := nonempty_iso_leftDerivedUpperStar_unit (ModuleCat.{u + 1} Λ) f
  exact ⟨(rightDerivedUpperShriek _ (pullback.fst f f)).mapIso ι.symm ≪≫ (e.app (𝟙_ _)).symm⟩

omit [HasTateTwist Λ] [IsSeparated f] in
include d in
/-- Blueprint `lem-pur-diagonal-base-change`: Base change for the dualizing object of a
projection

The symmetric statement: `ω_{p₂} ≅ Lp₁^* ω_f`. -/
theorem nonempty_iso_dualizingComplex_pullbackSnd [QuasiSeparatedSpace Y] [QuasiCompact f] :
    Nonempty (dualizingComplex Λ (pullback.snd f f) ≅
      (L((pullback.fst f f)^*[ModuleCat.{u + 1} Λ])).obj
        (dualizingComplex Λ f)) := by
  obtain ⟨e⟩ := nonempty_iso_leftDerivedUpperStar_comp_rightDerivedUpperShriek Λ (d := d) f
    (IsPullback.of_hasPullback f f)
  obtain ⟨ι⟩ := nonempty_iso_leftDerivedUpperStar_unit (ModuleCat.{u + 1} Λ) f
  exact ⟨(rightDerivedUpperShriek _ (pullback.snd f f)).mapIso ι.symm ≪≫ (e.app (𝟙_ _)).symm⟩

omit [HasTateTwist Λ] [IsSeparated f] in
include d in
/-- Blueprint `lem-pur-diagonal-base-change`: Base change for the dualizing object of a
projection

The section invariant of the diagonal `Δ : X ⟶ X ×_Y X`, a closed section of `p₁`, is the
dualizing complex of `f`: since `Δ ≫ p₂ = 𝟙 X`,

`𝒞(p₁, Δ) = LΔ^* ω_{p₁} ≅ LΔ^* Lp₂^* ω_f ≅ L(𝟙 X)^* ω_f ≅ ω_f`. -/
theorem nonempty_iso_sectionInvariant_diagonal [QuasiSeparatedSpace Y] [QuasiCompact f] :
    Nonempty (sectionInvariant Λ (pullback.fst f f) (pullback.diagonal f) ≅
      dualizingComplex Λ f) := by
  obtain ⟨e⟩ := nonempty_iso_dualizingComplex_pullbackFst Λ (d := d) f
  exact ⟨(L((pullback.diagonal f)^*[ModuleCat.{u + 1} Λ])).mapIso e ≪≫
    (leftDerivedUpperStarCompSectionIso _ _ _ (pullback.diagonal_snd f)).app _⟩

/-- Blueprint `sk-thm-smooth-purity`: Finite-coefficient smooth purity

**Smooth purity, finite coefficients.** For `f : X ⟶ Y` smooth separated of pure relative
dimension `d`, `Y` separated of finite type over a field, and a finite coefficient ring `Λ`
whose exponent is invertible on `X`,

`ω_f = Rf^! Λ_Y ≅ Λ_X(d)[2d]`,

canonically, compatibly with base change and additively in the twist under composition of
smooth morphisms.

This is also blueprint `thm-pur-diagonal-dualizing-object`. The proof is the diagonal argument.
Let `W = X ×_Y X` and `Δ : X ⟶ W` the diagonal, a closed section of the smooth projection
`p₁`.
1. `𝒞(p₁, Δ) ≅ ω_f` by smooth base change
   (`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_diagonal`); `f` is quasi-compact,
   being compactifiable over the locally noetherian `Y`
   (`AlgebraicGeometry.HasCompactification.quasiCompact_of_locallyOfFiniteType`).
2. `𝒞(p₁, Δ) ≅ Λ_X(d)[2d]`, the section invariant of a section of a smooth morphism
   (`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_twistShift_of_section`). Near the
   diagonal there are étale coordinates `x₁, …, x_d` of `W` over `X` cutting out `Δ`; the
   classes `∂κ(x₁) ∪ ⋯ ∪ ∂κ(x_d)` of these frames are restrictions of the Thom class of the zero
   section of `𝔸^d`, invertible over a base of finite type over the field, and they glue to a
   fundamental class of `Δ` with `RΔ^! (Λ_W(d)[2d]) ≅ Λ_X`. The co-projection formula and
   `RΔ^! ω_{p₁} ≅ R(Δ ≫ p₁)^! Λ_X = Λ_X` turn this into `𝒞(p₁, Δ) ≅ Λ_X(d)[2d]`.

Step 2 replaces the blueprint's deformation to the normal cone of `Δ` (`sk-thm-dnc`,
`AlgebraicGeometry.Etale.nonempty_iso_sectionInvariant_normalCone`) followed by vector-bundle
purity for its normal bundle: the fundamental class of `Δ` is glued directly from the
coordinate frames, as for regular immersions (`sk-thm-regular`), whose frame classes agree on
overlaps by frame independence. -/
theorem nonempty_iso_dualizingComplex_twistShift [HasTateTwist.IsNormalized Λ]
    {k : Type u} [Field k]
    (aY : Y ⟶ Spec (.of k)) [IsSeparated aY] [LocallyOfFiniteType aY] :
    Nonempty (dualizingComplex Λ f ≅
      (twistShift Λ X d).obj (constantComplex Λ X)) := by
  have : QuasiSeparatedSpace Y := quasiSeparatedSpace_of_quasiSeparated aY
  have : QuasiCompact f := HasCompactification.quasiCompact_of_locallyOfFiniteType f aY
  have := SmoothOfRelativeDimension.smooth d f
  have : HasInvertibleExponent Λ (pullback f f) := .of_hom (pullback.fst f f)
  obtain ⟨e₁⟩ := nonempty_iso_sectionInvariant_diagonal Λ (d := d) f
  obtain ⟨e₂⟩ := nonempty_iso_sectionInvariant_twistShift_of_section Λ d (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) (f ≫ aY)
  exact ⟨e₁.symm ≪≫ e₂⟩

end Etale

end AlgebraicGeometry
