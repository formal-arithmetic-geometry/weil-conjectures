/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.RingTheory.Localization.FractionRing

import Mathlib.RingTheory.Etale.StandardEtale
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.RingTheory.Polynomial.RationalRoot
import Sheaf.AlgebraicGeometry.FiniteEtaleNormalGenericComponents
import Mathlib.RingTheory.Ideal.GoingUp
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Sheaf.AlgebraicGeometry.UnramifiedMaximalIdealResidueCriterion
import Sheaf.RingTheory.CompleteDVRFiniteNormalization
import Sheaf.NumberTheory.DvrGaloisDegreeData
import Mathlib.FieldTheory.KummerPolynomial

/-! # Artin–Schreier pole tests over a complete DVR

Source: Stacks Project, More on Algebra, Tag 09F0, lemma-pre-characteristic-p-case,
cases (A), (B), (C), specialized to complete DVRs.
(blueprint: lem-sfb-epp-artin-schreier-valuation-tests)
-/

@[expose] public section

set_option autoImplicit false

universe u v

open Polynomial IsLocalRing

namespace IsDiscreteValuationRing

/-- The three Artin–Schreier pole tests for a complete DVR. The algebra H is the
specified quotient, presented by the E-algebra equivalence eH; its distinguished root
is the image under eH of the polynomial variable. Case (A) allows a split H.

Source: Stacks Project, More on Algebra, Tag 09F0, lemma-pre-characteristic-p-case,
cases (A), (B), (C), specialized to complete DVRs; Tag 09EM for completeness.
(blueprint: lem-sfb-epp-artin-schreier-valuation-tests)

Proof of (A):
1. For an integral coefficient, the monic quotient over R is finite free by
   lem-weil-pbc-monic-quotient-free. The derivative is -1, so eliminating the
   derivative-inverse generator in lem-weil-pbc-standard-etale-monic-derivative
   makes this quotient finite etale.
2. A DVR is Noetherian and normal by lem-weil-pbc-pid-noetherian-normal. Apply
   lem-sfb-finite-etale-normal-generic-components to Spec R. Integrality in a finite
   product is coordinatewise: project a monic equation in one direction; multiply
   annihilating monic equations for the finitely many coordinates in the other.
   Thus the finite etale quotient is exactly the integral closure, also in the split case.
3. By lem-weil-pbc-integral-maximal-contracts-maximal each maximal ideal contracts
   to the maximal ideal of R. Etaleness implies unramifiedness and local finite type
   by def-weil-etale-morphism. The criterion
   lem-trf-unramified-maximal-ideal-residue-criterion, using R localized at its own
   maximal ideal equal to R, gives the ideal equality and finite separable residue map.

Proof of (B):
1. Extend the normalized valuation of R to E by fractions. If b has nonnegative
   valuation, b^p-b cannot have negative valuation. If b has negative valuation,
   factoring out the smaller uniformizer power leaves a unit plus an element of the
   maximal ideal, hence v(b^p-b)=p v(b). This cannot equal -n when p does not divide n;
   b=0 is excluded by the nonzero pole coefficient. By
   lem-sfb-epp-artin-schreier-presentation the quotient is a normal separable field
   of degree p. Use lem-per-complete-dvr-finite-normalization to obtain its complete
   DVR integral closure with a local inclusion of R.
2. Write z for the adjoined root, w for the normalized valuation of D, and e=w(pi)>0.
   Base units stay units, so w(a)=-ne. The equation forces w(z)<0 and gives
   p w(z)=-ne, hence p divides e. Apply lem-exc-dvr-galois-degree-data: there is just
   one maximal ideal, so p=ef with f positive. Thus e=p and f=1. The residue map is
   an isomorphism. Writing pi as a unit times a pth power of a uniformizer gives
   the asserted equality of ideals.

Proof of (C):
1. Put h=n/p, c=pi^(n-h), and F(Y)=Y^p-cY-u. Then h>=1 and n-h=(p-1)h>0.
   By lem-weil-pbc-monic-quotient-free, B=R[Y]/F is free of rank p with special
   fibre k[Y]/(Y^p-u_bar). By lem-weil-pbc-x-pow-p-minus-t-irreducible the
   non-pth-power hypothesis makes this fibre a field of degree p, with basis
   1,y_bar,...,y_bar^(p-1). Apply lem-sfb-finite-free-field-fibre-dvr: B is a DVR,
   R embeds in B, and the maximal ideal of B is pi B.
2. The substitutions y=pi^h T and T=pi^(-h)y give inverse generic-fibre maps,
   since F(pi^h T)=pi^n(T^p-T-a). A DVR with uniformizer pi has fraction field
   B[1/pi], so the original quotient is a field of degree p. Regard B as
   R[pi^h T] in it. The inclusion is local, since its field fibre contains k.
   The uniqueness clause of lem-per-complete-dvr-finite-normalization identifies
   B with D and gives completeness. This proves the ideal equality and residue
   presentation, including its specified generator.
3. Every residue element has a representative sum of a_i y_bar^i for 0<=i<p.
   In characteristic p its pth power is the sum of a_i^p u_bar^i, in the image
   of k. The same basis gives degree p, proving every residue assertion.
-/
theorem artinSchreier_valuation_tests
    (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [IsAdicComplete (maximalIdeal R) R]
    (E : Type v) [Field E] [Algebra R E] [IsFractionRing R E]
    (p : ℕ) [Fact p.Prime] [CharP R p] (a : E)
    (H : Type v) [CommRing H] [Algebra E H] [Algebra R H] [IsScalarTower R E H]
    (eH : AdjoinRoot (X ^ p - X - C a) ≃ₐ[E] H) :
    (a ∈ Set.range (algebraMap R E) →
      ∀ (q : Ideal (integralClosure R H)) [q.IsMaximal],
        ∃ (_ : IsLocalHom (algebraMap R (Localization.AtPrime q))),
          (maximalIdeal R).map (algebraMap R (Localization.AtPrime q)) =
              q.map (algebraMap (integralClosure R H)
                (Localization.AtPrime q)) ∧
            Module.Finite (ResidueField R) (ResidueField (Localization.AtPrime q)) ∧
            Algebra.IsSeparable (ResidueField R) (ResidueField (Localization.AtPrime q))) ∧
    (∀ (π : R) (_ : Irreducible π) (n : ℕ) (u₀ : Rˣ),
      0 < n → ¬ p ∣ n →
      a = (algebraMap R E π)⁻¹ ^ n * algebraMap R E (u₀ : R) →
      IsField H ∧
        Module.finrank E H = p ∧
        ∃ (_ : IsDomain H)
          (_ : IsDiscreteValuationRing (integralClosure R H))
          (_ : IsLocalHom (algebraMap R (integralClosure R H))),
          IsAdicComplete
              (maximalIdeal (integralClosure R H))
              (integralClosure R H) ∧
            Function.Bijective
              (algebraMap (ResidueField R)
                (ResidueField (integralClosure R H))) ∧
            (maximalIdeal R).map
                (algebraMap R (integralClosure R H)) =
              maximalIdeal (integralClosure R H) ^ p) ∧
    (∀ (π : R) (_ : Irreducible π) (n : ℕ) (u₀ : Rˣ),
      0 < n → p ∣ n →
      (∀ c : ResidueField R, c ^ p ≠ residue R (u₀ : R)) →
      a = (algebraMap R E π)⁻¹ ^ n * algebraMap R E (u₀ : R) →
      IsField H ∧
        Module.finrank E H = p ∧
        integralClosure R H =
          Algebra.adjoin R
            {algebraMap E H
              ((algebraMap R E π) ^ (n / p)) * eH (AdjoinRoot.root (X ^ p - X - C a))} ∧
        ∃ (_ : IsDomain H)
          (_ : IsDiscreteValuationRing (integralClosure R H))
          (_ : IsLocalHom (algebraMap R (integralClosure R H))),
          IsAdicComplete
              (maximalIdeal (integralClosure R H))
              (integralClosure R H) ∧
            (maximalIdeal R).map
                (algebraMap R (integralClosure R H)) =
              maximalIdeal (integralClosure R H) ∧
            Module.finrank (ResidueField R) (ResidueField (integralClosure R H)) = p ∧
            (∀ x : ResidueField (integralClosure R H),
              ∃ c : ResidueField R,
                x ^ p = algebraMap (ResidueField R)
                  (ResidueField (integralClosure R H)) c) ∧
            ∃ (y : integralClosure R H)
              (e : AdjoinRoot (X ^ p - C (residue R (u₀ : R))) ≃ₐ[R]
                ResidueField (integralClosure R H)),
              (y : H) =
                  algebraMap E H
                    ((algebraMap R E π) ^ (n / p)) * eH (AdjoinRoot.root (X ^ p - X - C a)) ∧
                e (AdjoinRoot.root (X ^ p - C (residue R (u₀ : R)))) =
                  residue (integralClosure R H) y) := by
  sorry

end IsDiscreteValuationRing
