module

public import Sheaf.RingTheory.PermissibleBasisChartData
public import WeilConjectures.RingTheory.GradedAlgebra.Standard
import Sheaf.RingTheory.ProjectiveOrderTriangularCoordinates
import Sheaf.RingTheory.ProjectiveOrderCompletedNormalForm

/-! # Homogeneous syzygies lifting leading projective-order relations

Source: Hironaka, Certain numerical characters of singularities (1970),
Lemma 17, pp.172–173, with (13.2), (14.2), and (16.1)–(16.2).
(blueprint: lem-trf-projective-order-leading-syzygies).

This is the finite-jet assertion in the uncompleted local ring. The existing
`Hironaka.InOrderSpace` includes homogeneity and the prescribed order after
dehomogenization at zero. A finite output index set is encoded as `Fin n`.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Hironaka

/-- Leading relations between projective-order forms are generated, to the next
filtration level, by evaluations of homogeneous polynomial syzygies.

Source: Hironaka (1970), Lemma 17, pp.172–173; finite-jet adaptation of the
completed-coefficient assertion, using (13.2), (14.2), and (16.1)–(16.2).
(blueprint: lem-trf-projective-order-leading-syzygies).

Proof (the six steps of the accepted DAG split):
1. For b=0 take the empty output family. Otherwise use
`lem-trf-projective-order-triangular-coordinates` and permute the nonzero
coordinate labels. Write U=k[sigma] with positive weights q_i and write each
phi_j=P_j(sigma) with P_j weighted homogeneous of weight d_j, by separating
weights and using algebraic independence. With no pivots the nonempty family
of nonzero positive-degree forms cannot occur.
2. Apply `lem-trf-projective-order-completed-normal-form`. Expand beta_j in
rho^A z^B omega^gamma over its coefficient field F. Retain the finitely many
terms T_j of weight e-d_j; all lower coefficients vanish by the order formula,
and beta_j-T_j has order at least e-d_j+1. The coefficient comparison gives
delta(phi_j)-P_j^{epsilon_0}(rho) of order at least d_j+1, so the assumed
relation implies that sum_j T_j P_j^{epsilon_0}(rho) has order at least e+1.
3. This finite normal expansion has pure weight e, so it must vanish. For
each occurring pair (B,gamma), set h=e-|B|-|gamma| and collect the rho
coefficients as weighted homogeneous polynomials Q_j of weight h-d_j.
Uniqueness gives sum_j Q_j P_j^{epsilon_0}=0. Discard zero tuples; every
remaining pair has 1<=h<=e, and Q_j=0 when h<d_j.
4. For each retained pair, choose a basis over epsilon_0(k) of the finite
span of its coefficients in F. Expanding in this basis produces polynomials
D_{B,gamma,nu,j} over k, with the same weights and vanishing conditions.
Coefficientwise linear independence and injectivity of epsilon_0 give
sum_j D_{B,gamma,nu,j} P_j=0 in k[S]. This uses only finite polynomial
coefficient calculations, not containment of the original k in F.
5. Index by the retained triples, put C_vj=D_vj(sigma), and use U=k[sigma]
to obtain the asserted order-space membership and polynomial identities.
Lift each basis scalar u_nu to a residue representative in L_0 and put
a_v=lift(u_nu) z^B omega^gamma in L. It has order at least e-h_v, and its
difference from u_nu z^B omega^gamma has completed order at least e-h_v+1.
6. Apply the completed normal form's coefficient comparison to D_vj.
Multiplying the two congruences shows that a_v delta(C_vj) agrees with its
corresponding term in T_j modulo the power e-d_j+1. Sum and use the estimate
for beta_j-T_j. Preservation of orders under L to its completion gives the
asserted congruence in L itself. Empty output, zero coefficients, constant
C_vj, e=1, and empty variable tuples are included. -/
theorem projective_order_leading_syzygies
    {k : Type u} [Field k] (r b e : ℕ)
    (p : PrimeSpectrum (MvPolynomial {i : Fin (r + 1) // i ≠ 0} k))
    (he : 1 ≤ e)
    (d : Fin b → ℕ) (φ : Fin b → MvPolynomial (Fin (r + 1)) k)
    (hd : ∀ j : Fin b, 1 ≤ d j ∧ d j ≤ e)
    (hφ_ne : ∀ j : Fin b, φ j ≠ 0)
    (hφ : ∀ j : Fin b, InOrderSpace r p (d j) (φ j))
    (β : Fin b → Localization.AtPrime p.asIdeal)
    (hβ : ∀ j : Fin b, β j ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ (e - d j))
    (hsum : (∑ j : Fin b, β j *
      algebraMap _ (Localization.AtPrime p.asIdeal)
        (MvPolynomial.dehomogenizeX k 0 (φ j))) ∈
      IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ (e + 1)) :
    ∃ (n : ℕ) (h : Fin n → ℕ) (a : Fin n → Localization.AtPrime p.asIdeal)
      (C : Fin n → Fin b → MvPolynomial (Fin (r + 1)) k),
      (∀ v : Fin n, 1 ≤ h v ∧ h v ≤ e) ∧
      (∀ v : Fin n, a v ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ (e - h v)) ∧
      (∀ (v : Fin n) (j : Fin b),
        (h v < d j → C v j = 0) ∧
        (d j ≤ h v → InOrderSpace r p (h v - d j) (C v j))) ∧
      (∀ v : Fin n, (∑ j : Fin b, C v j * φ j) = 0) ∧
      (∀ j : Fin b, β j - ∑ v : Fin n, a v *
        algebraMap _ (Localization.AtPrime p.asIdeal)
          (MvPolynomial.dehomogenizeX k 0 (C v j)) ∈
        IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ (e - d j + 1)) := by
  sorry

end Hironaka
