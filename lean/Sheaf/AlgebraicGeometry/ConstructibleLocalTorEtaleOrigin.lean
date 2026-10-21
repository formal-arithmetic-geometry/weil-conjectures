/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q11
-/
module

public import Sheaf.AlgebraicGeometry.CoefficientAffineConstructibleProEtaleModules
public import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparisonData
public import Sheaf.AlgebraicGeometry.ProEtaleTorLocalGlobal
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Sheaf.AlgebraicGeometry.ConstructibleProEtaleComparison
import Sheaf.AlgebraicGeometry.ProEtaleFiniteTorComparisonNoetherian
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor

/-!
# Etale origin of constructible complexes locally of finite Tor dimension

Source: Stacks Project, proetale.tex, Tags 09C2 and 09AL
(blueprint: lem-sfb-constructible-local-tor-etale-origin).

We use the recorded coefficient-sized small sites and their constant ring sheaves.
The inverse image of a derived object C is expressed using a cochain representative P:
Q(P) is isomorphic to C, and Q of its canonical termwise comparison pullback is isomorphic
to M. Exactness makes this precisely the inverse image on derived categories, independent
of the representative. No inverse-image functor or tensor product is chosen anew.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

/-- On a quasi-compact quasi-separated scheme with discrete Noetherian coefficients,
constructible cohomology and locally finite Tor dimension are equivalent to bounded
constructible etale origin with finite Tor amplitude. The local condition tests every
module sheaf on every covering slice, with a possibly different ordered interval on
each covering member. The etale interval is uniform. The complex P only represents C;
its image is the actual canonical termwise comparison pullback, not an arbitrary map.

Source: Stacks Project, Tag 09C2, lemma-describe-constructible-complexes, (2) and (4)
at n = 1, and Tag 09AL, lemma-compare-constructible-derived
(blueprint: lem-sfb-constructible-local-tor-etale-origin).

Proof:
1. Apply lem-sfb-proetale-tor-local-global to the local Tor condition. Quasi-compactness
   gives one interval [a,b] for all global module tests, including when X is empty.
2. Test against the constant ring module in degree zero. The K-flat tensor construction
   of def-weil-derived-tensor identifies M tensor A_X with M. Thus M has cohomology only
   in [a,b]. Together with the assumed constructibility this gives bounded constructibility.
3. Apply sk-thm-pe-constructible-comparison: its bounded constructible equivalence is
   essentially surjective, giving a bounded constructible etale object C and an isomorphism
   from its derived comparison pullback to M. Choose a cochain representative P of C.
   The localization factorization of the comparison identifies the image of P with M.
4. Apply det-pe-finite-tor-comparison-noetherian to C and the global interval. Invariance
   under the comparison isomorphism gives the same Tor interval for C. This is the small
   argument omitted in the proof of Tag 09C2 (4).
5. Conversely, the bounded constructible comparison sends C to an object with constructible
   cohomology. The fixed-interval Noetherian Tor comparison sends its Tor bound to M.
   The reverse implication of lem-sfb-proetale-tor-local-global gives the required coverings
   and slice intervals. The termwise representative condition is exactly the comparison
   isomorphism by its canonical localization factorization. No completeness, boundedness
   or prior etale-origin assumption on M enters either direction. -/
theorem constructible_localTor_iff_etaleOrigin
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (A : Type (max v (u + 1))) [CommRing A] [IsNoetherianRing A]
    (M : ConstantCompletion.D (ConstantCompletion.constant
      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A)) :
    ((∀ q : ℤ, Scheme.IsCoefficientAffineLocallyConstructibleProEtaleModuleSheaf X A
        ((coefficientModelCohomology _ q).obj M)) ∧
      ∀ U : Scheme.coefficientProEtaleSiteModel.{u, v} X,
        ∃ S : Presieve U,
          Sieve.generate S ∈ Scheme.coefficientProEtaleModelTopology.{u, v} X U ∧
            ∀ (V : Scheme.coefficientProEtaleSiteModel.{u, v} X) (f : V ⟶ U), S f →
              ∃ a b : ℤ,
                HasCoefficientModelTorAmplitude
                  ((ConstantCompletion.constant
                    (Scheme.coefficientProEtaleModelTopology.{u, v} X) A).over V)
                  ((coefficientModelSliceRestriction
                    (ConstantCompletion.constant
                      (Scheme.coefficientProEtaleModelTopology.{u, v} X) A) V).obj M) a b) ↔
      ∃ C : ConstantCompletion.D (ConstantCompletion.constant
          (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A),
        Scheme.IsCoefficientBoundedConstructibleEtale X A C ∧
          (∃ a b : ℤ, HasCoefficientModelTorAmplitude _ C a b) ∧
          ∃ P : ConstantCompletion.Cx (ConstantCompletion.constant
              (Scheme.smallModelComparisonEtaleTopology.{u, v} X) A),
            Nonempty ((ConstantCompletion.Q _).obj P ≅ C) ∧
              Nonempty ((ConstantCompletion.Q _).obj
                ((constructibleComparisonComplexPullback X A).obj P) ≅ M) := by
  sorry

end AlgebraicGeometry.ProEtale
