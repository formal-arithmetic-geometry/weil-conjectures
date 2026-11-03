/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.IntegralQuotient.IntegralQuotientCoefficients
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.InternalQuotientRestriction
import WeilConjectures.AlgebraicGeometry.IntegralQuotient.CondensedFiniteQuotientRestrictionPreservesConstructible

/-! # Constructibility under finite quotient scalar restriction

Source: finite constant models in the principal-quotient coefficient argument.
(blueprint: lem-sf-condensed-finite-quotient-restriction-constructible). -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ProEtale
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralQuotient

/-- Restricting between positive finite uniformizer quotients preserves and
reflects constructibility, on the same finite constructible stratifications.
Source: current blueprint integral Hom reduction, finite coefficient comparison;
Bhatt--Scholze Section 6.8, Stacks 03DA and 03D2.
(blueprint: lem-sf-condensed-finite-quotient-restriction-constructible).
Proof: restriction from the smaller quotient to the integral ring preserves
local finite presentation. Indeed, the restricted regular quotient has a
one-relation finite free presentation by the normalized principal sequence;
restriction preserves finite sums and cokernels. Apply this on presentation
covers, refine those covers for cokernels, and retain the original finite
stratification. Restriction along the integral map to the larger quotient
reflects constructibility, giving preservation between finite quotients.
Reflection follows because restriction along a coefficient epimorphism is
fully faithful: extension of the restricted module is the original module,
and extension preserves local finite presentations. This includes empty
strata, the zero module and n = r = 0. -/
theorem finiteQuotientRestriction_constructible_iff
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (T : Scheme.{u}) (r n : ℕ) (h : n ≤ r)
    (M : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
      (condensedRingObj (finite l E n) T)) :
    IsConstructibleModuleObject (condensedRingObj (finite l E r) T)
        ((Mod.comap (coefficientMap (finiteMap l E r n h) T)).obj M) ↔
      IsConstructibleModuleObject (condensedRingObj (finite l E n) T) M := by
  have := epi_coefficientMap_finiteMap l E T r n h
  constructor
  · intro hM
    exact CondensedRing.constructible_of_comap_of_epi T _ _
      (coefficientMap (finiteMap l E r n h) T) M hM
  · exact finiteQuotientRestriction_constructible l E T r n h M

end AlgebraicGeometry.ProEtale.IntegralQuotient
