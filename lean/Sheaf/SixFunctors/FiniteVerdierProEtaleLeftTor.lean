/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q2
-/
module

public import Sheaf.SixFunctors.FiniteCoefficientVerdierData

/-! # Tor bounds for reduced pro-etale Verdier duals

Source: current blueprint cor-coef-finite-verdier.proof.md, the Hom comparison,
evaluation, double-dual and quotient cocycle sentences.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale
namespace WeilConjectures

/-- Scalar reduction of the pro-etale Verdier dual has the uniform dual interval.
This is only the left endpoint bound; it asserts no coefficient-comparison morphism.

Source: current blueprint cor-coef-finite-verdier.proof.md, final Tor-bound sentence;
DAG cor-coef-finite-verdier, step 5, final two sentences.
(blueprint: lem-coef-finite-verdier-proetale-left-tor).

Proof:
Represent K by the comparison pullback of an etale finite-Tor constructible K' with
interval [a,b], using lem-coef-finite-hom-site-descent and the fixed-module intrinsic
realization equivalence. By lem-weil-finite-duality-site-comparison, its dual for the
transported omega is the comparison pullback of D(K'). Etale Verdier preservation
gives D(K') interval [-b-2d,-a]. The flat constructible K-flat model of
lem-coef-finite-hom-domain-calculus preserves that interval after the coefficient
quotient. The scalar/site comparison identifies pro-etale reduction of D(K) with
comparison pullback of this etale reduction. Preservation of Tor intervals by site
comparison, followed by invariance under these isomorphisms, proves the claim.
The interval is ordered since a <= b and d >= 0. The argument uses every test module
sheaf through the Tor-preservation statements, not merely constructible test sheaves.
For the zero input or empty scheme it gives the same vanishing; identity quotients
are covered by the normalized scalar unit. -/
theorem finiteVerdier_proEtale_left_tor
    (D : FiniteFieldDatum.{u}) (l : ℕ) [Fact l.Prime] (hl : l ≠ D.p)
    (E : Type u) [Field E] [Algebra (Padic l) E]
    [FiniteDimensional (Padic l) E] (d : ℕ) (X : Scheme.{u})
    (hd : topologicalKrullDim X ≤ (d : WithBot ℕ∞))
    [X.Over (Spec (.of D.k))]
    [IsSeparated (X ↘ Spec (.of D.k))]
    [LocallyOfFiniteType (X ↘ Spec (.of D.k))]
    [QuasiCompact (X ↘ Spec (.of D.k))]
    {n m : ℕ} (h : m ≤ n)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology X)
      (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))))
    (hK : finiteTorConstructibleProEtaleModule l E (n + 1) (Nat.succ_pos n) X K)
    (a b : ℤ) (hab : a ≤ b)
    (ht : Scheme.HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (n + 1))
      ((ProEtale.finiteCoefficientIntrinsicRealization X
        (Padic.coefficientExtensionRing l E (n + 1))).mapDerivedCategory.obj K) a b) :
    Scheme.HasProEtaleTorAmplitude X (Padic.coefficientExtensionRing l E (m + 1))
      ((ProEtale.finiteCoefficientIntrinsicRealization X
        (Padic.coefficientExtensionRing l E (m + 1))).mapDerivedCategory.obj
        ((pbcFixedScalarExtension (Scheme.ProEt.topology X)
          (finiteDualizingQuotient l E h)).obj
          (((finiteVerdierProEtaleHomAt (finiteDualizingCoeff l E n) X).obj (op K)).obj
            ((comparisonUpperStar (ModuleCat.{u + 1} (finiteDualizingCoeff l E n))
              X).mapDerivedCategory.obj (finiteDualizingEtaleTerm l E D X n)))))
      (-b - 2 * (d : ℤ)) (-a) := by
  sorry

end WeilConjectures
