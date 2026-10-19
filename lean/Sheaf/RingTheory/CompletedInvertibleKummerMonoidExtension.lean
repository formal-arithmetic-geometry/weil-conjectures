/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q36
-/
module

public import Sheaf.RingTheory.FormalMonoidExtensionModel
import Sheaf.TraceFormula.FsFaceSharpening
import WeilConjectures.RingTheory.FiniteCompletionFactorIdempotent
import Mathlib.RingTheory.FiniteType
import WeilConjectures.RingTheory.LocalCompletionQuotient
import WeilConjectures.RingTheory.PowerSeriesFieldCohenRegularComplete
import WeilConjectures.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.FiniteEtaleFormalMonoidCoefficientLift
import Sheaf.RingTheory.FormalMonoidImplicitElimination
import Sheaf.RingTheory.TameKummerGroupAlgebraCompletion

/-!
# Completed local normal forms for invertible Kummer monoid extensions

Source: Illusie--Laszlo--Orgogozo, Travaux de Gabber, Exposé VI 2.2--2.3,
printed pp. 72--73; the arbitrary-unit-face and character-twist refinement of the DAG
(blueprint: lem-per-completed-invertible-kummer-monoid-extension).
-/

@[expose] public section

set_option autoImplicit false

universe u v w

namespace Algebra

/-- Invertible Kummer extensions preserve the equal- and mixed-characteristic completed
monoid models, with the actual nonunit monomial ideal and the selected residue field.
`IsLocalRing A` includes nonzeroness. Monoid notation is multiplicative, so positive
multiples and annihilation of the group cokernel are expressed by powers.
The published `chartSharpMonoid`, `CompletedLocalModel`, and
`HasExtendedFormalMonoidModel` retain the localized faces, coefficient rings,
parameter reduction, and continuity in both directions.

Source: ILO VI 2.2--2.3, printed pp. 72--73, with the explicit chart-twist refinement
(blueprint: lem-per-completed-invertible-kummer-monoid-extension).

Proof plan:
1. Choose finite generators of Q. The Kummer equations make their monomials integral
   over A and exhibit a finite spanning family for C. Finite-type Noetherianity and
   lem-weil-pbc-finite-completion-factor-idempotent identify the completion at q with
   its selected factor after completing A, preserving monomials.
2. The local map A to B reflects units. Apply lem-trf-fs-face-sharpening to G and F.
   Saturation and the Kummer condition show N F^gp is contained in h(G^gp). Thus the
   inclusion of unit-face groups has finite cokernel killed by N. The sharp map
   beta from S to T has inverse image of zero equal to zero.
3. Split the free sharp group quotients to write R_G = U direct-sum S and
   Q_F = V direct-sum T. The chart map is (h_U(u)+c(s), beta(s)). The given epsilon
   gives the unit twist on S; no extension of epsilon to Q^gp is required.
4. Impose unit relations first. By lem-per-tame-kummer-group-algebra-completion,
   the selected factor K is local finite etale over the completed base and has
   residue field kappa(q). Unit groups may have torsion.
5. Set E = k[[t]] or V[[t]]. The power-series/Cohen regular-complete theorem and
   lem-per-finite-etale-formal-monoid-coefficient-lift give a complete regular
   coefficient ring D with residue field kappa(q) and K = D[[S]]/(f).
6. Lift the twist character on a basis of the free group S^gp to units of D[[S]].
   Balancing monomial tensors, then applying the local-completion quotient theorem,
   gives D[[S direct-sum T]]/(f, Y^beta(s)-v(s)X^s). All rings are Noetherian by
   finite-type and completion permanence.
7. Apply lem-per-formal-monoid-implicit-elimination with u(s)=v(s)^(-1). Its
   quotient is D[[T]], fixing coefficients on the stratum. In the mixed case the
   image of theta is eta, so the quotient is D[[T]]/(eta).
8. On the stratum eta reduces to the coefficientwise image of theta at S=0.
   Since theta is congruent to p modulo the old monomials and parameters, this
   element has nonzero p cotangent component in E. The coefficient-lift lemma
   preserves it in D, giving membership in m_D and nonmembership in its square.
9. Each nonface Q monomial becomes a unit times a nonzero T monomial, and every
   nonzero T class has a representative q-f with q outside F. Thus the two
   generated ideals agree. The completion comparisons are continuous both ways.
   The same arguments cover zero parameters and the trivial sharp monoids.
-/
theorem completed_invertible_kummer_monoid_extension
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (R : Type v) [CommMonoid R] (Q : Type w) [CommMonoid Q]
    (_hR : AlgebraicGeometry.IsFineSaturatedMonoid R)
    (_hQ : AlgebraicGeometry.IsFineSaturatedMonoid Q) (h : R →* Q)
    (_hh : Function.Injective h)
    (_hkummer : ∀ q : Q, ∃ d : ℕ, 0 < d ∧ ∃ r : R, h r = q ^ d)
    (_hgp : Function.Injective
      (GrothendieckGroup.lift ((GrothendieckGroup.of (M := Q)).comp h)))
    (_hfinite : Finite (GrothendieckGroup Q ⧸
      (GrothendieckGroup.lift ((GrothendieckGroup.of (M := Q)).comp h)).range))
    (N : ℕ) (_hN : 0 < N) (_hNunit : IsUnit (N : A))
    (_hkill : ∀ z : GrothendieckGroup Q, ∃ r : GrothendieckGroup R,
      GrothendieckGroup.lift ((GrothendieckGroup.of (M := Q)).comp h) r = z ^ N)
    (α : R →* A) (a : Multiplicative (chartSharpMonoid α) →* A)
    (ε : GrothendieckGroup R →* Aˣ)
    (_hα : ∀ r : Localization ((IsUnit.submonoid A).comap α),
      localizedUnitChart α r =
        (ε (unitChartGroupMap α r) : A) * a (Multiplicative.ofAdd
          (Additive.ofMul (Associates.mk r))))
    (q : Ideal (monoidChartTensor α h)) [q.IsPrime]
    (_hq : Ideal.comap (monoidChartTensorBase α h) q = IsLocalRing.maximalIdeal A) :
    ((∃ (n : ℕ)
        (e : AddMonoidAlgebra.CompletedLocalModel (IsLocalRing.ResidueField A)
          (chartSharpMonoid α) n ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A),
        ∀ s : chartSharpMonoid α,
          e (algebraMap (MvPolynomial (Fin n)
              (AddMonoidAlgebra (IsLocalRing.ResidueField A) (chartSharpMonoid α))) _
            (MvPolynomial.C (AddMonoidAlgebra.single s (1 : IsLocalRing.ResidueField A)))) =
            algebraMap A _ (a (Multiplicative.ofAdd s))) →
      AddMonoidAlgebra.HasExtendedFormalMonoidModel (Localization.AtPrime q)
        (chartSharpMonoid (localizedTensorMonomial α h q))
        (localizedTensorBoundary α h q) false) ∧
    ((∃ (V : Type (max u v w)) (_ : CommRing V) (_ : IsLocalRing V) (p : ℕ),
        IsCohenRing p V ∧
        Nonempty (IsLocalRing.ResidueField V ≃+* IsLocalRing.ResidueField A) ∧
        ∃ (n : ℕ) (θ : AddMonoidAlgebra.CompletedLocalModel V (chartSharpMonoid α) n),
          θ - (p : AddMonoidAlgebra.CompletedLocalModel V (chartSharpMonoid α) n) ∈
            AddMonoidAlgebra.completedLocalModelBoundaryIdeal V (chartSharpMonoid α) n ∧
          ∃ e : (AddMonoidAlgebra.CompletedLocalModel V (chartSharpMonoid α) n ⧸
              Ideal.span {θ}) ≃+* AdicCompletion (IsLocalRing.maximalIdeal A) A,
            ∀ s : chartSharpMonoid α,
              e (Ideal.Quotient.mk (Ideal.span {θ})
                (algebraMap (MvPolynomial (Fin n)
                    (AddMonoidAlgebra V (chartSharpMonoid α))) _
                  (MvPolynomial.C (AddMonoidAlgebra.single s (1 : V))))) =
                  algebraMap A _ (a (Multiplicative.ofAdd s))) →
      AddMonoidAlgebra.HasExtendedFormalMonoidModel (Localization.AtPrime q)
        (chartSharpMonoid (localizedTensorMonomial α h q))
        (localizedTensorBoundary α h q) true) := by
  sorry


end Algebra
