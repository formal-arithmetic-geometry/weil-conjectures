/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.CompactSupportCondensedRealization.CompactSupportCondensedRealization
public import WeilConjectures.AlgebraicGeometry.BrownTowerComparison.BrownTowerFiniteSiteComparison
public import WeilConjectures.SmoothPurity.Integral.IntegralExceptionalInverseImage
public import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparisonData
import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportOrdinaryComparison
import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportDerivedComparison
public import WeilConjectures.AlgebraicGeometry.CondensedSupportCoordinateComparison

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

open CompactSupportCondensedRealization AlgebraicGeometry.ProEtale

/-- The normalized comparison package exists uniquely, including all intermediate
ordinary and derived maps. Source: blueprint integral Hom display; Zheng 4.1, 4.10,
5.15; universal-unit characterization of integralExceptionalComparison
(blueprint: def-pur-integral-support-coordinate-comparison).

Proof: restrict the actual direct-image sections on the ringed sequence site through
integralExceptionalCoordinates. The quotient-ring maps send every residue class to
itself, so the resulting ordinary push comparisons are identity on sections after
the dependency's rightEvaluation and rightUnderlying maps. Those maps are invertible;
sections detect equality, hence these comparisons are unique. Transpose the open
push comparison using the two ordinary inverse/direct adjunctions to obtain openPull.
Exactness and the identity on constant coefficient sections make it invertible.
Transpose openPull using the two extension/restriction adjunctions to obtain
openExtension with the stated Hom equation; Yoneda makes this map unique. Exact
localization supplies derivedOpen and its displayed representative equation, uniquely
since precomposition with Q is fully faithful. For proper image, exact quotient
coordinates preserve K-injectives. The right-derived universal property transports
the ordinary properPush comparison to derivedProper with precisely the displayed
unit equation; uniqueness of right-derived pairs makes this comparison unique.
These arguments determine every data field, so proof irrelevance yields uniqueness
of the entire Normalized package. All constructions keep the actual quotient
transitions, and no comparison is selected from undetermined mere existence. -/
theorem normalized_existsUnique : ∃! _B : Normalized l E S G H D, True := by
  obtain ⟨B, _, hB⟩ := ordinary_existsUnique l E S G H D
  obtain ⟨R, _, hR⟩ := derived_existsUnique l E S G H D B
  refine ⟨⟨B, R⟩, trivial, ?_⟩
  rintro ⟨B', R'⟩ _
  have h := hB B' trivial
  subst B'
  have h := hR R' trivial
  subst R'
  rfl

/-- The uniquely normalized comparison data. Its data are determined by section,
transpose, representative and universal-unit equations in normalized_existsUnique.
Source: blueprint integral Hom display
(blueprint: def-pur-integral-support-coordinate-comparison). -/
def normalized : Normalized l E S G H D :=
  (normalized_existsUnique l E S G H D).choose

/-- Compatibility alias to the current native condensed support comparison.
Source: the native comparison anchored by
`def-pur-integral-support-coordinate-comparison`
(blueprint: def-pur-integral-support-coordinate-comparison).

The current anchor constructs this comparison from the fixed ordinary and derived
section-operation maps.  This alias exposes that same comparison through the
historical module without reintroducing the withdrawn quotient-coordinate model.
-/
def beta (c : Compactification f) :
    CondensedRing.rightDerivedLowerShriekOfCompactification Λ c ⋙
        (derivedEquivalence Λ Y).functor ≅
      (derivedEquivalence Λ X).functor ⋙
        AlgebraicGeometry.ProEtale.ModuleRingedComparison.sectionSupport Λ c :=
  AlgebraicGeometry.ProEtale.ModuleRingedComparison.supportCoordinateComparison Λ c

/-- The compatibility alias is definitionally the current DAG anchor.
(blueprint: def-pur-integral-support-coordinate-comparison). -/
theorem beta_eq_supportCoordinateComparison (c : Compactification f) :
    beta Λ c = AlgebraicGeometry.ProEtale.ModuleRingedComparison.supportCoordinateComparison
      Λ c := by
  rfl

end WeilConjectures.PurIntegralSupportComparison
