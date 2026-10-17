/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Replete
public import WeilConjectures.CategoryTheory.Monoidal.Mod.Abelian
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible

/-!
# Compactness of constructible sheaves with `ℓ`-adic coefficients: the inputs

For the `ℓ`-adic coefficient rings `Λ = E, 𝒪_E, ℚ̄_ℓ` on a separated finite-type scheme over a
field `k` which is finite or separably closed, the compactness of constructible sheaves in
`Loc(Dᵇc(X, Λ))` (blueprints `sk-thm-constructible-compactness`, `sk-prop-int-compactness`) is
reduced in `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.CompactConstructible` to
the exactness of countable products of `Λ_X`-modules and to inputs on the ind-constructible
heart.

## Main results

* `AlgebraicGeometry.Scheme.ProEt.hasExactLimitsOfShape_discrete_nat_mod`: countable products of
  sheaves of modules over a ring object of abelian sheaves on `X_proét` are exact (blueprint
  `sk-prop-pe-products`), by repleteness of the pro-étale topos.

## Sorried input

* `isIndConstructibleHeart_continuousMapRingObj`, `isIndConstructibleHeart_padicIntegersRingObj`,
  `isIndConstructibleHeart_padicAlgClRingObj` (blueprints `sk-prop-ind-heart` (2),
  `det-prop-int-compactness-compact` (1)): the ind-constructible sheaves are closed under
  kernels, cokernels, extensions and direct sums.
* `hasIndConstructibleExtBound_continuousMapRingObj`,
  `hasIndConstructibleExtBound_padicIntegersRingObj`, `hasIndConstructibleExtBound_padicAlgClRingObj`
  (blueprint `sk-cor-ind-heart-ii`): the uniform bound and continuity of `Ext` out of a
  constructible sheaf into ind-constructible sheaves.
-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory MonObj Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [Abelian C] [MonoidalPreadditive C]
  {R : C} [MonObj R] [PreservesFiniteColimits (tensorLeft R)]

/-- If towers of epimorphisms in `C` have epimorphic projections `lim Xₙ ⟶ X₀`, so do towers of
`R`-modules: the forgetful functor preserves limits and epimorphisms, and reflects epimorphisms. -/
lemma epiπAppZeroOfEpi_of_epiπAppZeroOfEpi [HasLimitsOfShape ℕᵒᵖ C] (h : EpiπAppZeroOfEpi C) :
    EpiπAppZeroOfEpi (Mod C R) := by
  intro F c hc hF
  have : (forget R : Mod C R ⥤ C).IsRightAdjoint := (freeForgetAdjunction R).isRightAdjoint
  have : (forget R : Mod C R ⥤ C).PreservesEpimorphisms :=
    NormalMonoCategory.preservesEpimorphisms_of_preservesCokernels _
  apply (forget R : Mod C R ⥤ C).epi_of_epi_map
  exact h (F := F ⋙ forget R) (isLimitOfPreserves (forget R) hc) fun n ↦ (forget R).map_epi _

end CategoryTheory.Mod

namespace AlgebraicGeometry.Scheme

/-- Repleteness of the affine pro-étale topos, for abelian sheaves: the projection `lim Fₙ ⟶ F₀`
of a tower of epimorphisms is an epimorphism. -/
lemma AffineProEt.epi_π_app_zero_of_epi_addCommGrpCat {S : Scheme.{u}} :
    EpiπAppZeroOfEpi (Sheaf (AffineProEt.topology S) AddCommGrpCat.{u + 1}) := by
  intro F c hc hF
  have h {M N : Sheaf (AffineProEt.topology S) AddCommGrpCat.{u + 1}} (φ : M ⟶ N) :
      Sheaf.IsLocallySurjective φ ↔ Epi φ :=
    Sheaf.isLocallySurjective_iff_epi' _ φ
  simp_rw [← h] at hF ⊢
  exact AffineProEt.isLocallySurjective_π_app_zero_of_isLocallySurjective_map hc hF

/-- Repleteness of the pro-étale topos, for abelian sheaves (Bhatt–Scholze, Proposition 4.2.8):
the projection `lim Fₙ ⟶ F₀` of a tower of epimorphisms is an epimorphism. -/
lemma ProEt.epi_π_app_zero_of_epi_addCommGrpCat {S : Scheme.{u}} :
    EpiπAppZeroOfEpi (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) := by
  intro F c hc hF
  let e := (AffineProEt.toProEt S).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
    (AffineProEt.topology S) (ProEt.topology S)
  apply e.epi_of_epi_map
  exact AffineProEt.epi_π_app_zero_of_epi_addCommGrpCat (F := F ⋙ e) (isLimitOfPreserves e hc)
    fun n ↦ e.map_epi _

/-- Blueprint `sk-prop-pe-products`: countable products of sheaves of modules over a ring object
of abelian sheaves on the pro-étale site are exact. -/
instance ProEt.hasExactLimitsOfShape_discrete_nat_mod {S : Scheme.{u}}
    (R : Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) [MonObj R] :
    HasExactLimitsOfShape (Discrete ℕ) (Mod (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) R) :=
  have : HasLimitsOfSize.{u + 1, u + 1}
      (Mod (Sheaf (ProEt.topology S) AddCommGrpCat.{u + 1}) R) :=
    IsGrothendieckAbelian.hasLimits _
  have := CountableAB4Star.of_epi_π_app_zero
    (Mod.epiπAppZeroOfEpi_of_epiπAppZeroOfEpi (R := R) ProEt.epi_π_app_zero_of_epi_addCommGrpCat)
  CountableAB4Star.ofShape ℕ

end AlgebraicGeometry.Scheme
