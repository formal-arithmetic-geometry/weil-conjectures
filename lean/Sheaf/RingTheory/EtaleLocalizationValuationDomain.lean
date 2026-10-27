module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Valuation.ValuationRing

import Sheaf.AlgebraicGeometry.EtaleComparison
import Sheaf.RingTheory.IndEtaleUniverseTransport
import Sheaf.RingTheory.WeaklyEtaleTor

/-! # Etale localizations over the closed point of a valuation domain

Source: Stacks Project, more-algebra.tex, Tag 0ASJ,
lemma-etale-extension-valuation-ring, statement and first proof paragraph
(blueprint: lem-trf-etale-localization-valuation-domain).
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace AlgebraicGeometry

/-- The localization of an etale algebra over a valuation domain at a prime above
its maximal ideal is a valuation domain, and the natural map is injective and local.
Source: Stacks Project, Tag 0ASJ, lemma-etale-extension-valuation-ring, statement
and first proof paragraph (blueprint: lem-trf-etale-localization-valuation-domain).

Proof:
1. Apply clauses (1) and (4) of det-pe-morphisms-etale-comparison to the affine
   spectrum map. The algebra map and tensor multiplication are flat, giving the
   weakly etale ring-map condition of def-weil-pbc-ind-etale-algebra.
2. Apply lem-trf-flat-localized-field-descent at the maximal ideal of A and q.
   This gives an injective local map from the localization of A at its maximal
   ideal to B_q. Every denominator in that localization of A is a unit, so its
   canonical map from A is an isomorphism. The composite is the natural map
   displayed below. An element maps into q B_q exactly when it maps into q,
   exactly when it belongs to the maximal ideal of A.
3. The local-ring clause of lem-trf-weak-dimension-one-valuation-criterion gives
   flat resolutions of length at most one for all A-modules. The final clause
   of lem-weil-pbc-weak-etale-tor transfers this bound to all B-modules.
4. Apply (i) implies (ii) of lem-trf-weak-dimension-one-valuation-criterion at q.
   It makes B_q an integral domain and a valuation ring. Together with step 2
   this gives all three conclusions, without any finiteness or rank hypothesis.
-/
theorem etale_localization_valuation_domain
    (A B : Type u) [CommRing A] [IsDomain A] [ValuationRing A]
    [CommRing B] [Algebra A B]
    (hEtale : Etale (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (q : Ideal B) [q.IsPrime]
    (hq : Ideal.comap (algebraMap A B) q = IsLocalRing.maximalIdeal A) :
    Function.Injective (algebraMap A (Localization.AtPrime q)) ∧
      Ideal.comap (algebraMap A (Localization.AtPrime q))
        (IsLocalRing.maximalIdeal (Localization.AtPrime q)) = IsLocalRing.maximalIdeal A ∧
      ∃ h : IsDomain (Localization.AtPrime q),
        @ValuationRing (Localization.AtPrime q) _ h := by
  sorry

end AlgebraicGeometry
