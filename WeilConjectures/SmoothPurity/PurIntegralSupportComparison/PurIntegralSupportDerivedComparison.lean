/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparisonData

/-! # Canonical compact-support comparison in strict quotient coordinates

Source: current blueprint sk-prop-sp-integral-adjunction, outer Hom comparisons;
Zheng Constructions 4.1 and 5.15, Lemma 4.10; the universal-unit normalization of
integralExceptionalComparison_characterization
(blueprint: def-pur-integral-support-coordinate-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option genCtorIdx false
attribute [-instance] WeilConjectures.IntegralHom.derivedCategory
attribute [-instance] WeilConjectures.integralExceptionalSystemDerived
attribute [-instance] WeilConjectures.integralExceptionalLevelDerived
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry SheafOfModules Opposite
open WeilConjectures AlgebraicGeometry.Scheme
attribute [local instance 5000] AlgebraicGeometry.strictEtaleLevelDerived
  AlgebraicGeometry.strictEtaleSystemDerived
attribute [local instance] BrownTowerComparison.ProCompact.openAdditive
namespace WeilConjectures.PurIntegralSupportComparison

variable (l : ℕ) [Fact l.Prime] (E : Type u) [NormedField E]
  [NormedAlgebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E]

variable {X Y : Scheme.{u}} {f : X ⟶ Y} {c : Compactification f}
  (S : StrictEtaleCompactSupport (integralExceptionalIntegers l E)
    (integralExceptionalUniformizer l E) c)
  (G : EtaleTowerBrownAdjunction S) (H : BrownTowerComparison.FiniteEvaluation S G)
  (D : BrownTowerComparison.TransportData S G H)

/-- A fixed ordinary normalized comparison admits a unique derived extension.
Source: Stacks 05RU, 0D6E; Zheng Lemma 4.10; blueprint integral Hom display
(blueprint: lem-pur-integral-support-derived-comparison).

Proof: apply the fixed ordinary openExtension and inverse properPush termwise to
complexes. Naturality makes these chain maps and fixes their component equations.
For open extension, combine the two exact localization factorizations with the
termwise isomorphism. The fully faithful precomposition with the localization Q
lifts this to derivedOpen and gives exactly derivedOpen_factors; it also gives
uniqueness. The coordinate equivalences are exact and preserve K-injectives, so the
proper right-derived pairs transported through them are universal right-derived
pairs for the same ordinary proper direct image. Their unique comparison is an
isomorphism. The right-derived factorization equation, with properPush inverted,
is precisely derivedProper_unit. Uniqueness of right-derived transformations gives
uniqueness of derivedProper. Componentwise extensionality fixes the two chain-map
fields; proof irrelevance then identifies the entire Derived record. This argument
assumes the Ordinary record as a parameter and constructs no ordinary comparison. -/
theorem derived_existsUnique (B : Ordinary l E S G H D) :
    ∃! R : Derived l E S G H D B, True := by
  sorry

end WeilConjectures.PurIntegralSupportComparison
