/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import WeilConjectures.SixFunctors.ProEtale.TraceFormula.Frobenius

/-!
# Restricting a model Frobenius to open and closed pieces

Let `(K, φ)` be a Weil complex on `X = X₀ ×_{Spec k} s` whose Frobenius is the base change of
the `q`-power Frobenius `F₀` of `X₀`. An open or closed immersion `g₀ : Y₀ ⟶ X₀` is stable under
`F₀`, so its base change `f : Y = X ×_{X₀} Y₀ ⟶ X` is stable under the Frobenius of `X`, and the
restricted Weil complex `Lf^* K` (`WeilComplex.upperStarPull`) again has a model Frobenius, with
model `Y₀`. This provides the pieces of the localization step (Step 5) of the proof of blueprint
`thm-trf-coefficient-morphism-trace-formula`.

## Main results

- `AlgebraicGeometry.Scheme.Hom.IsFrobenius.exists_comp_eq_of_isOpenImmersion`,
  `AlgebraicGeometry.Scheme.Hom.IsFrobenius.exists_comp_eq_of_isClosedImmersion`: the
  `q`-power Frobenius restricts to open and closed subschemes.
- `AlgebraicGeometry.ProEtale.WeilComplex.IsModelFrobenius.exists_upperStarPull`: the
  restriction of a Weil complex with model Frobenius to the base change of a subscheme of the
  model stable under the Frobenius has a model Frobenius.
- `AlgebraicGeometry.ProEtale.WeilComplex.isCompl_range_of_isPullback`: base change preserves
  complementary open and closed pieces.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits

namespace AlgebraicGeometry

namespace Scheme.Hom.IsFrobenius

variable {X₀ U₀ : Scheme.{u}} {F₀ : X₀ ⟶ X₀} {q : ℕ}

/-- The `q`-power Frobenius of `X₀` restricts to every open subscheme `j₀ : U₀ ⟶ X₀`: there is
a `q`-power Frobenius `F_U` of `U₀` with `F_U ≫ j₀ = j₀ ≫ F₀`. -/
theorem exists_comp_eq_of_isOpenImmersion {k : Type u} [Field k] [Finite k]
    (f₀ : X₀ ⟶ Spec (.of k)) (hF₀ : F₀.IsFrobenius (Nat.card k)) (j₀ : U₀ ⟶ X₀)
    [IsOpenImmersion j₀] :
    ∃ F : U₀ ⟶ U₀, F.IsFrobenius (Nat.card k) ∧ F ≫ j₀ = j₀ ≫ F₀ :=
  sorry

/-- The `q`-power Frobenius of `X₀` restricts to every closed subscheme `i₀ : Z₀ ⟶ X₀`: there is
a `q`-power Frobenius `F_Z` of `Z₀` with `F_Z ≫ i₀ = i₀ ≫ F₀`. -/
theorem exists_comp_eq_of_isClosedImmersion {k : Type u} [Field k] [Finite k]
    (f₀ : X₀ ⟶ Spec (.of k)) (hF₀ : F₀.IsFrobenius (Nat.card k)) (i₀ : U₀ ⟶ X₀)
    [IsClosedImmersion i₀] :
    ∃ F : U₀ ⟶ U₀, F.IsFrobenius (Nat.card k) ∧ F ≫ i₀ = i₀ ≫ F₀ :=
  sorry

end Scheme.Hom.IsFrobenius

namespace ProEtale.WeilComplex

variable {A : Type u'} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {s X : Scheme.{u}} {aX : X ⟶ s}
  (W : WeilComplex (A := A) aX) {k : Type u} [Field k] [Finite k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k)} {σ : s ⟶ Spec (.of k)} {p : X ⟶ X₀}

/-- Let `W` have a model Frobenius with model `X₀`, and let `g₀ : Y₀ ⟶ X₀` be a morphism stable
under the `q`-power Frobenius of `X₀`, in the sense that the Frobenius `F₀` of `X₀` restricts to a
`q`-power Frobenius of `Y₀` along `g₀` (for instance an open or a closed immersion). Then the
base change `f : Y ⟶ X` of `g₀` along `p` is stable under the Frobenius of `X`, and the restricted
Weil complex `Lf^* K` has a model Frobenius with model `Y₀`. -/
theorem IsModelFrobenius.exists_upperStarPull (hΦ : W.IsModelFrobenius f₀ σ p)
    {Y Y₀ : Scheme.{u}} (f : Y ⟶ X) (g₀ : Y₀ ⟶ X₀) (q : Y ⟶ Y₀) (hsq : IsPullback q f g₀ p)
    (hg₀ : ∀ F₀ : X₀ ⟶ X₀, F₀.IsFrobenius (Nat.card k) →
      ∃ F : Y₀ ⟶ Y₀, F.IsFrobenius (Nat.card k) ∧ F ≫ g₀ = g₀ ≫ F₀) :
    ∃ (g : Y ⟶ Y) (sq : CommSq g f f (W.frobeniusIterate 1)),
      (W.upperStarPull f rfl g sq).IsModelFrobenius (g₀ ≫ f₀) σ q :=
  sorry

/-- Base change along `p : X ⟶ X₀` preserves complementary pieces: if the ranges of `j₀` and
`i₀` are complementary in `X₀`, the ranges of their base changes `j`, `i` are complementary
in `X`. -/
theorem isCompl_range_of_isPullback {U U₀ Z Z₀ : Scheme.{u}} {j : U ⟶ X} {j₀ : U₀ ⟶ X₀}
    {qU : U ⟶ U₀} {i : Z ⟶ X} {i₀ : Z₀ ⟶ X₀} {qZ : Z ⟶ Z₀} (hU : IsPullback qU j j₀ p)
    (hZ : IsPullback qZ i i₀ p) (h : IsCompl (Set.range j₀.base) (Set.range i₀.base)) :
    IsCompl (Set.range j.base) (Set.range i.base) :=
  sorry

end ProEtale.WeilComplex

end AlgebraicGeometry
