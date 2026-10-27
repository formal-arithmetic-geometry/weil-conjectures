module

public import Sheaf.RingTheory.PermissibleBasisChartData
public import WeilConjectures.RingTheory.GradedAlgebra.Standard
public import Mathlib.RingTheory.AdicCompletion.Algebra
public import Mathlib.RingTheory.MvPowerSeries.Rename
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Sheaf.RingTheory.ParameterChartCompletionSubstitution
import WeilConjectures.RingTheory.ExistsCoefficientSubring
import WeilConjectures.RingTheory.CompletionDimension
import WeilConjectures.RingTheory.AdicCompletionNoetherianOfQuotient
import WeilConjectures.RingTheory.CompletionRegularLocal
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.RegularLocalRing.Polynomial
import Mathlib.Algebra.Polynomial.FieldDivision

/-! # Completed normal coordinates at a projective point

Source: Hironaka, Certain numerical characters of singularities (1970), Lemma 14,
(14.1)--(14.2), p.169, and Remarks (16.1)--(16.2), pp.171--172.
(blueprint: lem-trf-projective-order-completed-normal-form).

The auxiliary declarations only name the explicit rings, coordinates, and finite
partial sums of this statement. Convergence means agreement modulo every power;
the coordinate isomorphisms identify these powers and hence are continuous in
both directions for the maximal-ideal topologies. The coefficient field is a
subring that is a field, rather than a subfield of an ambient division ring.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace Hironaka

namespace ProjectiveOrderCompletion

variable (k : Type u) [Field k] (r e : ℕ)

/-- The affine polynomial ring, retaining the nonzero projective labels.
Source: Hironaka (1970), §13, pp.168--169.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
abbrev AffinePolynomial := MvPolynomial {i : Fin (r + 1) // i ≠ 0} k

/-- The suffix polynomial subalgebra `k[t_(e+1),...,t_r]` inside `k[t_1,...,t_r]`.
Source: Hironaka (1970), Lemma 14, p.169.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
def suffixPolynomial : Subalgebra k (AffinePolynomial k r) :=
  Algebra.adjoin k {f | ∃ i : {i : Fin (r + 1) // i ≠ 0},
    e < i.val.val ∧ f = MvPolynomial.X i}

variable (p : PrimeSpectrum (AffinePolynomial k r))

/-- The given local ring `L`.
Source: Hironaka (1970), Lemma 14, p.169.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
abbrev Local := Localization.AtPrime p.asIdeal

/-- The suffix local ring `L₀`, at the contraction of the specified prime.
Source: Hironaka (1970), Lemma 14, p.169.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
abbrev SuffixLocal :=
  Localization.AtPrime
    (PrimeSpectrum.comap (suffixPolynomial k r e).val.toRingHom p).asIdeal

/-- The natural inclusion of the suffix local ring, induced by polynomial inclusion.
Source: Hironaka (1970), Lemma 14, p.169.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
abbrev suffixInclusion : SuffixLocal k r e p →+* Local k r p :=
  Localization.localRingHom _ p.asIdeal (suffixPolynomial k r e).val.toRingHom rfl

/-- The maximal-ideal completion of `L`.
Source: Hironaka (1970), (14.2), p.169.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
abbrev Completed := AdicCompletion (IsLocalRing.maximalIdeal (Local k r p)) (Local k r p)

/-- The maximal-ideal completion of `L₀`.
Source: Hironaka (1970), (14.2), p.169.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
abbrev SuffixCompleted :=
  AdicCompletion (IsLocalRing.maximalIdeal (SuffixLocal k r e p)) (SuffixLocal k r e p)

/-- The extended maximal ideal `N L̂`.
Source: Hironaka (1970), Remark (16.2), p.172.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
def completedIdeal : Ideal (Completed k r p) :=
  (IsLocalRing.maximalIdeal (Local k r p)).map
    (algebraMap (Local k r p) (Completed k r p))

/-- The extended maximal ideal `N₀ L̂₀`.
Source: Hironaka (1970), (14.2), p.169.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
def suffixCompletedIdeal : Ideal (SuffixCompleted k r e p) :=
  (IsLocalRing.maximalIdeal (SuffixLocal k r e p)).map
    (algebraMap (SuffixLocal k r e p) (SuffixCompleted k r e p))

/-- Dehomogenization followed by localization: `δ(f)=f(1,t)/1`.
Source: Hironaka (1970), §13, pp.168--169.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
def delta : MvPolynomial (Fin (r + 1)) k →+* Local k r p :=
  (algebraMap (AffinePolynomial k r) (Local k r p)).comp
    (MvPolynomial.dehomogenizeX k 0).toRingHom

/-- The translated coordinates `z_i=t_i-a_i`, indexed from zero in Lean.
Source: Hironaka (1970), (14.1), p.169.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
def translated (he : e ≤ r) (a : Fin e → SuffixLocal k r e p) (i : Fin e) : Local k r p :=
  algebraMap (AffinePolynomial k r) (Local k r p)
    (MvPolynomial.X ⟨⟨i.val + 1, by omega⟩, by simp⟩) - suffixInclusion k r e p (a i)

/-- The weight `q·A+|β|+|γ|`, with the bounded exponents represented by finite types.
Source: Hironaka (1970), Remark (16.2), p.172.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
def expansionWeight {e h : ℕ} (q : Fin e → ℕ) (A : Fin e → ℕ)
    (β : ∀ i : Fin e, Fin (q i)) (γ : Fin h → ℕ) : ℕ :=
  (∑ i : Fin e, q i * A i) + (∑ i : Fin e, (β i).val) + ∑ j : Fin h, γ j

/-- The finite partial sum of weight below `n` in the normal expansion.
The boxes `A_i,γ_j<n` contain every exponent of weight below `n` when `q_i≥1`.
Source: Hironaka (1970), (14.2) and Remark (16.2), pp.169,172.
(blueprint: lem-trf-projective-order-completed-normal-form). -/
def expansionTruncation {F C : Type u} [CommRing F] [CommRing C] {e h : ℕ}
    (q : Fin e → ℕ) (ι : F →+* C) (ρ z : Fin e → C) (ω : Fin h → C)
    (c : (Fin e → ℕ) → (∀ i : Fin e, Fin (q i)) → (Fin h → ℕ) → F) (n : ℕ) : C :=
  ∑ A : Fin e → Fin n, ∑ β : (∀ i : Fin e, Fin (q i)), ∑ γ : Fin h → Fin n,
    if expansionWeight q (fun i ↦ (A i).val) β (fun j ↦ (γ j).val) < n then
      ι (c (fun i ↦ (A i).val) β (fun j ↦ (γ j).val)) *
        (∏ i : Fin e, ρ i ^ (A i).val) * (∏ i : Fin e, z i ^ (β i).val) *
          ∏ j : Fin h, ω j ^ (γ j).val
    else 0

end ProjectiveOrderCompletion

open ProjectiveOrderCompletion

/-- Completed normal form, its weighted order, and the change of coefficient field.
Source: Hironaka (1970), Lemma 14 and (14.1)--(14.2), p.169;
Remarks (16.1)--(16.2), pp.171--172.
(blueprint: lem-trf-projective-order-completed-normal-form).

Proof (the nine accepted DAG steps):
1. The suffix localizations and L are Noetherian regular local by
lem-weil-pbc-polynomial-ring-field-regular-ring. Successive localization inverts
exactly the same denominators. Apply lem-trf-polynomial-localization-order-reflection
to get N^a intersect R_j = M_j^a. Thus rho_j belongs to M_j^(q_j).
2. Modulo the next suffix maximal ideal, rho_j is monic of degree q_j and has
order at least q_j in K[t_j] localized at a nonzero prime. By
lem-pur-polynomial-field-pid write that prime as (f), f monic irreducible.
Bezout cancels denominators and gives f^(q_j) dividing rho_j. Degrees force
f to be linear. Descending through all j gives the natural residue isomorphism.
3. Lift each residue t_i to a_i in L_0. Then z_i=t_i-a_i is in N, and the prime
in L_0[t_1,...,t_e] equals (N_0,z), since the latter already has field quotient.
Hence L is the localization of L_0[z] at (N_0,z), fixing the base.
4. Choose regular parameters omega in L_0. By lem-weil-pbc-completion-regular-local,
lem-weil-pbc-completion-dimension, and
lem-weil-pbc-completion-noetherian-quotient-noetherian, its completion is complete
regular local of the same dimension. Apply lem-weil-pbc-cohen-coefficient-ring-exists:
in equal characteristic its coefficient ring is a field. Its residue section gives F.
Apply lem-trf-parameter-chart-completion-substitution with empty chart to get the
compatible power-series coordinates with the prescribed parameter and coefficient images.
5. By lem-weil-pbc-adic-completion-mod-power the map to each completed quotient
has kernel N^a, so it preserves all orders. Its kernel is the intersection of
these powers, zero by lem-weil-pbc-krull-intersection-jacobson. It is injective.
6. Frobenius additivity (or q_i=1 in characteristic zero) writes rho_i as
z_i^(q_i) plus later z_l^(q_i) terms and b_i in L_0. Set z=0 to see b_i is in
(omega)^(q_i). The initial form is Z_i^(q_i) plus later Z powers and a homogeneous
polynomial in W. Coefficients of later Z powers are their residues in F.
7. In each degree the products H^A Z^beta W^gamma form a basis: their leading
monomials Z^(qA+beta) W^gamma biject the ordinary monomials by Euclidean division.
The finite change-of-basis matrix is triangular with diagonal one.
8. Subtract successive homogeneous components using this basis. Completeness gives
the convergent expansion; the least nonzero weight and independence of the basis
give uniqueness and the order formula. Zero has order infinity; empty tuples work.
9. Define epsilon_0 by reduction k to L_0/N_0 and inversion of the F residue map.
For each coefficient a, a-epsilon_0(a) lies in (omega). Multiply by rho^A of
order at least q·A=d and sum to obtain the congruence modulo N^(d+1).
-/
theorem projective_order_completed_normal_form
    {k : Type u} [Field k] (r e : ℕ) (he : e ≤ r)
    (p : PrimeSpectrum (AffinePolynomial k r)) (q : Fin e → ℕ)
    (hq : ∀ i : Fin e, 1 ≤ q i) (hmono : Monotone q)
    (hchar : ∀ i : Fin e, if ringChar k = 0 then q i = 1
      else ∃ n : ℕ, q i = ringChar k ^ n)
    (c : Fin e → Fin (r + 1) → k)
    (σ : Fin e → MvPolynomial (Fin (r + 1)) k)
    (hσ : ∀ i : Fin e,
      σ i = MvPolynomial.X ⟨i.val + 1, by omega⟩ ^ q i +
        ∑ l ∈ Finset.univ.filter (fun l : Fin (r + 1) ↦ i.val + 1 < l.val ∨ l = 0),
          MvPolynomial.C (c i l) * MvPolynomial.X l ^ q i)
    (hU : Algebra.adjoin k {f : MvPolynomial (Fin (r + 1)) k |
        ∃ d : ℕ, InOrderSpace r p d f} = Algebra.adjoin k (Set.range σ)) :
    ∃ (a : Fin e → SuffixLocal k r e p) (h : ℕ) (ω : Fin h → SuffixLocal k r e p),
      (∀ i : Fin e, translated k r e p he a i ∈ IsLocalRing.maximalIdeal (Local k r p)) ∧
      (∀ j : Fin h, ω j ∈ IsLocalRing.maximalIdeal (SuffixLocal k r e p)) ∧
      ∃ (F : Subring (SuffixCompleted k r e p)), IsField F ∧
      ∃ (ε : F ≃+* IsLocalRing.ResidueField (SuffixLocal k r e p))
        (j : SuffixCompleted k r e p →+* Completed k r p)
        (E₀ : MvPowerSeries (Fin h) F ≃+* SuffixCompleted k r e p)
        (E : MvPowerSeries (Fin h ⊕ Fin e) F ≃+* Completed k r p),
        (∀ b : F, ε b = AdicCompletion.evalOneₐ
          (IsLocalRing.maximalIdeal (SuffixLocal k r e p)) b.val) ∧
        Function.Bijective (IsLocalRing.ResidueField.map (suffixInclusion k r e p)) ∧
        Function.Injective (suffixInclusion k r e p) ∧
        Function.Injective j ∧
        (∀ b : SuffixLocal k r e p,
          j (algebraMap _ (SuffixCompleted k r e p) b) =
            algebraMap _ (Completed k r p) (suffixInclusion k r e p b)) ∧
        (∀ b : F, E₀ (MvPowerSeries.C b) = b.val) ∧
        (∀ b : F, E (MvPowerSeries.C b) = j b.val) ∧
        (∀ i : Fin h, E₀ (MvPowerSeries.X i) =
          algebraMap _ (SuffixCompleted k r e p) (ω i)) ∧
        (∀ i : Fin h, E (MvPowerSeries.X (Sum.inl i)) =
          j (algebraMap _ (SuffixCompleted k r e p) (ω i))) ∧
        (∀ i : Fin e, E (MvPowerSeries.X (Sum.inr i)) =
          algebraMap _ (Completed k r p) (translated k r e p he a i)) ∧
        (∀ f : MvPowerSeries (Fin h) F,
          j (E₀ f) = E (MvPowerSeries.rename Sum.inl f)) ∧
        (∀ n : ℕ, Ideal.comap E₀.toRingHom (suffixCompletedIdeal k r e p ^ n) =
          Ideal.span (Set.range (MvPowerSeries.X : Fin h → MvPowerSeries (Fin h) F)) ^ n) ∧
        (∀ n : ℕ, Ideal.comap E.toRingHom (completedIdeal k r p ^ n) =
          Ideal.span (Set.range
            (MvPowerSeries.X : Fin h ⊕ Fin e → MvPowerSeries (Fin h ⊕ Fin e) F)) ^ n) ∧
        Function.Injective (algebraMap (Local k r p) (Completed k r p)) ∧
        (∀ b : Local k r p, adicOrder (IsLocalRing.maximalIdeal (Local k r p)) b =
          adicOrder (completedIdeal k r p) (algebraMap _ (Completed k r p) b)) ∧
        (∀ v : Completed k r p,
          ∃ coeff : (Fin e → ℕ) → (∀ i : Fin e, Fin (q i)) → (Fin h → ℕ) → F,
            (∀ n : ℕ, v - expansionTruncation q (j.comp F.subtype)
              (fun i ↦ algebraMap _ (Completed k r p) (delta k r p (σ i)))
              (fun i ↦ algebraMap _ (Completed k r p) (translated k r e p he a i))
              (fun i ↦ j (algebraMap _ (SuffixCompleted k r e p) (ω i))) coeff n ∈
                completedIdeal k r p ^ n) ∧
            (∀ coeff' : (Fin e → ℕ) → (∀ i : Fin e, Fin (q i)) → (Fin h → ℕ) → F,
              (∀ n : ℕ, v - expansionTruncation q (j.comp F.subtype)
                (fun i ↦ algebraMap _ (Completed k r p) (delta k r p (σ i)))
                (fun i ↦ algebraMap _ (Completed k r p) (translated k r e p he a i))
                (fun i ↦ j (algebraMap _ (SuffixCompleted k r e p) (ω i))) coeff' n ∈
                  completedIdeal k r p ^ n) → coeff' = coeff) ∧
            adicOrder (completedIdeal k r p) v =
              ⨅ A : Fin e → ℕ, ⨅ β : (∀ i : Fin e, Fin (q i)), ⨅ γ : Fin h → ℕ,
                ⨅ (_ : coeff A β γ ≠ 0), (expansionWeight q A β γ : ℕ∞)) ∧
        (∀ (d : ℕ) (P : MvPolynomial (Fin e) k), P.IsWeightedHomogeneous q d →
          algebraMap _ (Completed k r p)
              (MvPolynomial.eval₂ (algebraMap k (Local k r p)) (delta k r p ∘ σ) P) -
            MvPolynomial.eval₂
              ((j.comp F.subtype).comp (ε.symm.toRingHom.comp
                ((IsLocalRing.residue (SuffixLocal k r e p)).comp
                  (algebraMap k (SuffixLocal k r e p)))))
              (fun i ↦ algebraMap _ (Completed k r p) (delta k r p (σ i))) P ∈
                completedIdeal k r p ^ (d + 1)) := by
  sorry

end Hironaka
