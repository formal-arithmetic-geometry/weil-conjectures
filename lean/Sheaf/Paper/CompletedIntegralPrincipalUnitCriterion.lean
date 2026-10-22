/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.Paper.DerivedCompleteUnrestricted
public import Sheaf.Paper.PrincipalKoszulStrictReplacement
public import Sheaf.Algebra.Homology.PrincipalQuotientCompletionModel

/-! # The principal quotient unit for completed integral coefficients

Source: Stacks Project, Tags 093M, 099B and 0A0E; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-weil-completed-integral-principal-unit-criterion).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_proEtTopology
attribute [-instance] WeilConjectures.integralOperationsCommHasDerivedCategory
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
attribute [-instance] WeilConjectures.integralOperationsAbLocallyBijective
attribute [-instance] WeilConjectures.integralOperationsAbSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abSheafify
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.abLocallyBijective
attribute [-instance] WeilConjectures.PrincipalKoszulStrictReplacement.siteSmall
attribute [local irreducible] HasDerivedCategory.standard
attribute [local instance 5000] WeilConjectures.integralTowerHasDerivedCategory
universe t u
open CategoryTheory CategoryTheory.Limits
namespace WeilConjectures

/-- Every normalized principal quotient completion computes the same complete locus.

Source: Stacks Project, Tags 093M, 099B and 0A0E; Bhatt--Scholze, Proposition 3.5.1.
(blueprint: lem-weil-completed-integral-principal-unit-criterion).

Proof: pass to the canonical small model of the pro-etale site in the coefficient
universe. Restriction is an exact equivalence of module categories, preserves all
products, and transports the uniformizer and its multiplication map. The completed
quotient comparison identifies the cokernel of its (n+1)-st power with the actual
constant residue sheaf; it identifies the quotient maps and all transitions, not
just the objects. On a flat K-flat representative tensor this presentation with the
representative. Exact countable products carry the resulting levelwise quasi-isomorphisms
to the signed Roos cones, with their zero shifted coordinate augmentations. Apply the
regular quotient completion unit criterion on the small model. Its normalized Roos
triangle condition is precisely the defining condition of IsDerivedComplete, after
transport along the resolution map and the representative isomorphism. The auxiliary
finite-field datum is absent from every ring and map in this calculation. The criterion
makes the specified unit invertible exactly on that locus and makes its output complete.
The universal left-derived property compares any supplied Model with this quotient
construction, preserving its counit and unit on K-flat representatives; localization
extends both equations to all objects. This proves the assertion for the supplied Model.
The argument includes the zero complex and the empty scheme and needs no
boundedness or constructibility assumption. -/
theorem completedIntegralPrincipalUnitCriterion
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] (Y : AlgebraicGeometry.Scheme.{t})
    (C : @PrincipalQuotientCompletion.Model.{t + 1, t, max u (t + 1), max u (t + 1) + 1}
      Y.ProEt inferInstance (essentiallySmallSelf.{u} _)
      (AlgebraicGeometry.Scheme.ProEt.topology Y) inferInstance
      (integralCoefficientAbSheafify.{t, u} Y)
      (integralCoefficientAbLocallyBijective.{t, u} Y)
      (completedIntegralCommRingSheafUnrestricted l E Y)
      (integralTowerHasDerivedCategory l E Y)
      (PrincipalKoszulStrictReplacement.uniformizer l E Y)) :
    ∀ K : DerivedCategory (integralTowerModules l E Y),
      IsDerivedCompleteUnrestricted l E Y K ↔ IsIso (C.unit.app K) := by
  sorry

end WeilConjectures
