/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportComparisonData
import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportOrdinaryExistence
import WeilConjectures.SmoothPurity.PurIntegralSupportComparison.PurIntegralSupportOrdinaryUniqueness

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

set_option linter.unusedVariables false in
/-- The section-normalized ordinary push comparisons, and their two open adjunction
transposes, exist uniquely.
Source: Zheng Construction 4.1, Lemma 4.10; blueprint integral Hom display
(blueprint: lem-pur-integral-support-ordinary-comparison).

Proof: identify the direct-image sections of sequence-site modules with their strict
quotient-coordinate sections. Both maps send a residue class to the same class, so
this identification commutes with scalar multiplication and all quotient transitions.
Use rightEvaluation and rightUnderlying to express it in the specified right-system
coordinates. The inverse identification is again the identity on sections, giving
openPush and properPush. Cancel the two underlying isomorphisms and use sectionwise
extensionality to prove uniqueness of each push comparison. Transport the ordinary
inverse/direct adjunction through the exact coordinate equivalences; its left-adjoint
uniqueness isomorphism gives openPull with the displayed transpose equation. Transport
extension/restriction in the same way to get openExtension. For uniqueness, evaluate
each transpose equation on the identity of the corresponding sequence-site pull or
extension object. Injectivity of the Hom adjunction and cancellation of openPull give
equality of the components. Naturality and proof irrelevance identify the records.
No right-derived functor or complex comparison is used in this argument. -/
theorem ordinary_existsUnique : ∃! B : Ordinary l E S G H D, True := by
  -- The two strict obligations are isolated in their own modules.
  obtain ⟨B⟩ := ordinary_exists l E S G H D
  refine ⟨B, trivial, ?_⟩
  intro B' _
  exact ordinary_unique l E S G H D B' B

end WeilConjectures.PurIntegralSupportComparison
