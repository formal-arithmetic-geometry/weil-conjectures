/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralGeometricComparisonData

/-! # A component of integral geometric comparison realization -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option synthInstance.maxSize 4096
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [local irreducible] AlgebraicGeometry.Scheme.residueField
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.Scheme WeilConjectures
namespace AlgebraicGeometry.ProEtale.IntegralGeometricComparison

/-- Construct the two smooth reconstruction packages on one geometric Frobenius square.
This asserts neither reindexing/limit compatibility, Tate comparison, completed exchange,
nor the integral exceptional transpose identity.

Source: latest blueprint, integral-adjunction-bijection, Normalization and Bijections;
geometric-equivariance Step 5, realization Steps 1 and 5.
(blueprint: lem-pur-geometric-smooth-reconstruction-setup).

Proof: retag the source copies by the geometric coefficient automorphism, so that the
horizontal scheme isomorphisms are linear. Separated finite-type structures transport
along these isomorphisms. Choose a compactification of the smooth morphism and use its
Cartesian pullback for the other side. The tower base-change theorem gives a, hb and the
invertible tower mate. Construct the four normalized integral coordinates by simultaneous
reduction and its total-limit adjunction. Apply integral-adjunction-bijection on both
compactifications with these same coordinates and tower adjunctions. Retain its actual
reconstruction packages; their unit-reduction identities give the last two fields of
SmoothPart. Transport the reconstructed right adjoints to the chosen integral right
adjoints by the unique counit-preserving comparison. The counit equations and the fixed
pullback models then give IntegralData. No rank-one hypothesis is used here: for general E
apply the integral adjunction theorem directly, rather than the rank-one final clause of
tower_exceptional_base_change. Empty schemes and dimension zero use the same adjunctions.
-/
theorem geometric_smooth_reconstruction_setup (P : PurityFiniteSetting.{u})
    (X₀ Y₀ : Over (Spec (CommRingCat.of P.field.k₀)))
    [IsSeparated X₀.hom] [LocallyOfFiniteType X₀.hom] [QuasiCompact X₀.hom]
    [IsSeparated Y₀.hom] [LocallyOfFiniteType Y₀.hom] [QuasiCompact Y₀.hom]
    (f₀ : X₀ ⟶ Y₀) [IsSeparated f₀.left] [LocallyOfFiniteType f₀.left]
    [QuasiCompact f₀.left] (d : ℕ)
    [SmoothOfRelativeDimension d (P.frobeniusMap f₀)]
    (b₀ : SpTowerShriek.Base P.coefficients.l P.extension)
    (o₀ : SpTowerShriek.Operations P.coefficients.l P.extension b₀)
    (q₀ : SpTowerCalculus.Coordinates P.coefficients.l P.extension b₀)
    (x₀ : SpTowerShriek.OpenExchange P.coefficients.l P.extension b₀ o₀)
    (_laws : SpTowerShriek.Laws P.coefficients.l P.extension b₀ o₀ x₀) :
  let l₀ := P.coefficients.l
  let E₀ := P.extension
  let geom := P.schemeGeometricFrobenius_squares X₀ Y₀ f₀ d
  letI : IsIso (P.frobeniusGaloisMap X₀) := geom.1
  letI : IsIso (P.frobeniusGaloisMap Y₀) := geom.2.1
  letI : ∀ x : (P.frobeniusFiber X₀).left,
      Invertible (l₀ : (P.frobeniusFiber X₀).left.residueField x) :=
    sfWeilPrimeInvertible P.field l₀ P.coefficients.different X₀
  letI : ∀ y : (P.frobeniusFiber Y₀).left,
      Invertible (l₀ : (P.frobeniusFiber Y₀).left.residueField y) :=
    sfWeilPrimeInvertible P.field l₀ P.coefficients.different Y₀
  ∃ (c₀ : Compactification (P.frobeniusMap f₀))
    (a₀ : SpTowerMate.Data l₀ E₀ b₀ o₀ q₀ geom.2.2.1 c₀)
    (hb₀ : IsIso (SpTowerMate.beta l₀ E₀ b₀ o₀ q₀ a₀ x₀))
    (s₀ : SpExceptionalBaseChange.IntegralData l₀ E₀ b₀ o₀ q₀ a₀),
    letI : QuasiCompact (P.frobeniusMap f₀) := s₀.quasiCompact
    letI : QuasiCompact (c₀.i ≫ c₀.g) := c₀.comm ▸ s₀.quasiCompact
    letI : HasCompactification (c₀.i ≫ c₀.g) :=
      (SpTowerGamma.factorization c₀.i c₀.g).hasCompactification
    let c₁ := c₀.ofIsPullback geom.2.2.1
    letI : QuasiCompact (c₁.i ≫ c₁.g) := c₁.comm ▸ s₀.quasiCompact'
    letI : HasCompactification (c₁.i ≫ c₁.g) :=
      (SpTowerGamma.factorization c₁.i c₁.g).hasCompactification
    Nonempty (SmoothPart l₀ E₀ b₀ o₀ q₀ a₀ s₀ d) ∧
      IsIso (SpTowerMate.mate l₀ E₀ b₀ o₀ q₀ a₀ x₀ hb₀) := by
  sorry

end AlgebraicGeometry.ProEtale.IntegralGeometricComparison
