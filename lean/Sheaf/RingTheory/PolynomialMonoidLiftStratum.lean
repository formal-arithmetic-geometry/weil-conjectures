module

public import Sheaf.RingTheory.CompleteToricModel
public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import WeilConjectures.RingTheory.CohenRing
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Defs
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Spectrum.Prime.Defs
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Ideal
import WeilConjectures.RingTheory.AdicCompletionNoetherian

/-! # Polynomial lifts and Laurent residue strata

Source: ILO VI 1.6, printed p. 70, and the agent-supplied polynomial lift and
residue-stratum calculation in the DAG (blueprint: lem-trf-polynomial-monoid-lift-stratum).
The polynomial rings, completion ideals and completions are the published
`ToricMonoid` constructions. Every tensor algebra structure below is constructed
from the canonical chart map.
-/

@[expose] public section

set_option autoImplicit false

universe u v w z

noncomputable section

namespace ToricMonoid

/-- Extend a monoid homomorphism to the polynomial monoid rings, fixing coefficients
and variables. Source: ILO VI 1.6, polynomial lift calculation
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
def polynomialChartMap (L : Type u) [CommRing L] {S : Type v} [AddCommMonoid S]
    {P : Type w} [AddCommMonoid P] (n : ℕ) (f : S →+ P) :
    PolynomialRing L S n →+* PolynomialRing L P n :=
  MvPolynomial.map (AddMonoidAlgebra.mapDomainRingHom L f)

/-- The integer monoid ring maps to the coefficient monoid ring and then to polynomial
constants. Source: ILO VI 1.6, polynomial lift calculation
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
def integerChartMap (L : Type u) [CommRing L] (S : Type v) [AddCommMonoid S] (n : ℕ) :
    AddMonoidAlgebra ℤ S →+* PolynomialRing L S n :=
  MvPolynomial.C.comp (AddMonoidAlgebra.mapRingHom S (Int.castRingHom L))

/-- The coefficient-and-variable ideal `(m_L,t)` in the Laurent coefficient ring.
Source: ILO VI 1.6, residue-stratum calculation
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
def polynomialParameterIdeal (L : Type u) [CommRing L] [IsLocalRing L]
    (P : Type v) [AddCommMonoid P] (n : ℕ) : Ideal (PolynomialRing L P n) :=
  Ideal.map (algebraMap L (PolynomialRing L P n)) (IsLocalRing.maximalIdeal L) ⊔
    Ideal.span (Set.range (MvPolynomial.X : Fin n → PolynomialRing L P n))

/-- The positive `T`-monomial ideal in `L[K ⊕ T][t]`.
Source: ILO VI 1.6, residue-stratum calculation
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
def polynomialStratumIdeal (L : Type u) [CommRing L] (K : Type v) [AddCommGroup K]
    (T : Type w) [AddCommMonoid T] (n : ℕ) : Ideal (PolynomialRing L (K × T) n) :=
  Ideal.span {b | ∃ t : T, t ≠ 0 ∧ b = MvPolynomial.C (AddMonoidAlgebra.single (0, t) (1 : L))}

/-- The polynomial lift `H_S ⊗[R₀] U`, with the chart-induced algebra structure.
Source: ILO VI 1.6, printed p. 70, polynomial lift calculation
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
abbrev PolynomialLift (L : Type u) [CommRing L] [IsLocalRing L]
    (S : Type v) [AddCommMonoid S] (P : Type w) [AddCommMonoid P] (n : ℕ) (f : S →+ P) :=
  letI := (polynomialChartMap L n f).toAlgebra
  TensorProduct (PolynomialRing L S n) (Complete L S n) (PolynomialRing L P n)

/-- The canonical map from `U` into the polynomial lift.
Source: ILO VI 1.6, printed p. 70, polynomial lift calculation
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
def polynomialLiftRight (L : Type u) [CommRing L] [IsLocalRing L]
    (S : Type v) [AddCommMonoid S] (P : Type w) [AddCommMonoid P] (n : ℕ) (f : S →+ P) :
    PolynomialRing L P n →+* PolynomialLift L S P n f :=
  letI := (polynomialChartMap L n f).toAlgebra
  Algebra.TensorProduct.includeRight.toRingHom

/-- The canonical map from `H_S` into the polynomial lift.
Source: ILO VI 1.6, printed p. 70, polynomial lift calculation
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
def polynomialLiftLeft (L : Type u) [CommRing L] [IsLocalRing L]
    (S : Type v) [AddCommMonoid S] (P : Type w) [AddCommMonoid P] (n : ℕ) (f : S →+ P) :
    Complete L S n →+* PolynomialLift L S P n f :=
  letI := (polynomialChartMap L n f).toAlgebra
  Algebra.TensorProduct.includeLeftRingHom

/-- Pure tensors in the polynomial lift with its specified scalar action.
Source: ILO VI 1.6, printed p. 70, polynomial lift calculation
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
def polynomialLiftTensor (L : Type u) [CommRing L] [IsLocalRing L]
    (S : Type v) [AddCommMonoid S] (P : Type w) [AddCommMonoid P] (n : ℕ) (f : S →+ P)
    (x : Complete L S n) (b : PolynomialRing L P n) : PolynomialLift L S P n f :=
  letI := (polynomialChartMap L n f).toAlgebra
  TensorProduct.tmul (PolynomialRing L S n) x b

/-- The ideal `IW` in the polynomial lift.
Source: ILO VI 1.6, printed p. 70, polynomial lift calculation
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
def polynomialLiftIdeal (L : Type u) [CommRing L] [IsLocalRing L]
    (S : Type v) [AddCommMonoid S] (P : Type w) [AddCommMonoid P] (n : ℕ) (f : S →+ P) :
    Ideal (PolynomialLift L S P n f) :=
  Ideal.map ((polynomialLiftRight L S P n f).comp (polynomialChartMap L n f))
    (completionIdeal L S n)

/-- The integer monoid tensor `H_S ⊗[ℤ[S]] ℤ[P]` with both canonical scalar actions.
Source: ILO VI 1.6, printed p. 70, polynomial lift calculation
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
abbrev IntegerPolynomialLift (L : Type u) [CommRing L] [IsLocalRing L]
    (S : Type v) [AddCommMonoid S] (P : Type w) [AddCommMonoid P] (n : ℕ) (f : S →+ P) :=
  letI := ((algebraMap (PolynomialRing L S n) (Complete L S n)).comp
    (integerChartMap L S n)).toAlgebra
  letI := (AddMonoidAlgebra.mapDomainRingHom ℤ f).toAlgebra
  TensorProduct (AddMonoidAlgebra ℤ S) (Complete L S n) (AddMonoidAlgebra ℤ P)

/-- Pure tensors in the integer monoid tensor with its canonical scalar actions.
Source: ILO VI 1.6, printed p. 70, polynomial lift calculation
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
def integerPolynomialLiftTensor (L : Type u) [CommRing L] [IsLocalRing L]
    (S : Type v) [AddCommMonoid S] (P : Type w) [AddCommMonoid P] (n : ℕ) (f : S →+ P)
    (x : Complete L S n) (b : AddMonoidAlgebra ℤ P) : IntegerPolynomialLift L S P n f :=
  letI := ((algebraMap (PolynomialRing L S n) (Complete L S n)).comp
    (integerChartMap L S n)).toAlgebra
  letI := (AddMonoidAlgebra.mapDomainRingHom ℤ f).toAlgebra
  TensorProduct.tmul (AddMonoidAlgebra ℤ S) x b

/-- The residue field of the prime of `A/(a)` over `N` agrees with that of `N`,
compatibly with the quotient map. The equality on images of `A` specifies the
canonical residue map, since these images generate the residue field as a field.
Source: ILO VI 1.6(ii), printed p. 70, and Stacks Tag 00CT
(blueprint: lem-trf-polynomial-monoid-lift-stratum). -/
def HasCompatibleQuotientResidueField (A : Type u) [CommRing A]
    (N : PrimeSpectrum A) (a : A) : Prop :=
  ∃ q : PrimeSpectrum (A ⧸ Ideal.span {a}),
    Ideal.comap (Ideal.Quotient.mk (Ideal.span {a})) q.asIdeal = N.asIdeal ∧
    ∃ e : N.asIdeal.ResidueField ≃+* q.asIdeal.ResidueField,
      ∀ b : A, e (algebraMap A N.asIdeal.ResidueField b) =
        algebraMap (A ⧸ Ideal.span {a}) q.asIdeal.ResidueField
          (Ideal.Quotient.mk (Ideal.span {a}) b)

/-- Polynomial lift and Laurent residue stratum of a formal monoid chart.
Source: ILO VI 1.6, printed p. 70; independent polynomial coefficient lift and
residue-stratum calculation (blueprint: lem-trf-polynomial-monoid-lift-stratum).

Proof: Choose finite nonzero generators of S and T and a basis of K. Every positive
S-monomial is divisible by a generator, so I is finitely generated. The coefficient
ring is Noetherian (a field or a Cohen DVR). Finite polynomial presentations give
Noetherianity of R₀ and U by lem-weil-pbc-finite-type-algebra-noetherian. Apply
lem-weil-pbc-adic-completion-noetherian to H_S. The tensors of the finitely many
Laurent and T-generators generate W over H_S, so W is also Noetherian.

On pure monomial tensors define the two displayed maps. Balancing follows by moving
coefficients and variables across the tensor, and moving [s] uses f(s). Both maps
preserve products and one. Their composites fix the displayed additive generators.
By lem-weil-pbc-adic-completion-mod-power (05GG, N=1), H_S/IH_S = R₀/I.
The map x⊗u ↦ x̄ū and u ↦ 1⊗u modulo IW are inverse: choose a polynomial lift
of x̄; its difference from x lies in IH_S, which vanishes modulo IW.

Sharpness of T makes constant coefficient E[T] → E a ring retraction with kernel J,
the positive T-monomial ideal. Thus r = pU + J and U/r = E/p. The parameter
hypothesis gives (m_L,t) ⊆ p. Positivity of the T-component of f puts IU in r
and IW in n. The canonical quotient isomorphism identifies primes containing IW
with primes of U containing IU and yields uniqueness of n and W/n = U/r.

Apply lem-weil-pbc-localization-at-prime-of-quotient (00CT) with the prime itself
to identify each residue field with the fraction field of its domain quotient.
The quotient maps agree on U and E, giving precisely the stated residue maps.
Finally θ-p is a sum of multiples of positive S-monomials and variables; all their
images and p belong to n. Hence θ ∈ n. Apply 00CT to (θ): localize the quotient
and then divide by its maximal ideal. The result is κ(n), compatibly with W.
-/
theorem polynomialMonoidLiftStratum (L : Type u) [CommRing L] [IsLocalRing L]
    (hL : IsField L ∨ ∃ p : ℕ, IsCohenRing p L)
    (S : Type v) [AddCommMonoid S] (T : Type w) [AddCommMonoid T]
    (hS : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative S))
    (hT : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative T))
    (hsharpS : ∀ s : S, IsUnit (Multiplicative.ofAdd s) → s = 0)
    (hsharpT : ∀ t : T, IsUnit (Multiplicative.ofAdd t) → t = 0)
    (K : Type z) [AddCommGroup K] [Module.Free ℤ K] [Module.Finite ℤ K]
    (f : S →+ K × T) (hβ : ∀ s : S, s ≠ 0 → (f s).2 ≠ 0) (n : ℕ) :
    (completionIdeal L S n).FG ∧
    IsNoetherianRing (PolynomialRing L S n) ∧ IsNoetherianRing (PolynomialRing L (K × T) n) ∧
    IsNoetherianRing (Complete L S n) ∧ IsNoetherianRing (PolynomialLift L S (K × T) n f) ∧
    (∃ e : PolynomialLift L S (K × T) n f ≃+* IntegerPolynomialLift L S (K × T) n f,
      (∀ (x : Complete L S n) (l : L) (p : K × T) (d : Fin n →₀ ℕ),
        e (polynomialLiftTensor L S (K × T) n f x
          (MvPolynomial.monomial d (AddMonoidAlgebra.single p l))) =
        integerPolynomialLiftTensor L S (K × T) n f
          (x * algebraMap (PolynomialRing L S n) (Complete L S n)
            (MvPolynomial.monomial d (AddMonoidAlgebra.single 0 l)))
          (AddMonoidAlgebra.single p 1)) ∧
      (∀ (x : Complete L S n) (p : K × T),
        e.symm (integerPolynomialLiftTensor L S (K × T) n f x
          (AddMonoidAlgebra.single p 1)) =
        polynomialLiftTensor L S (K × T) n f x
          (MvPolynomial.C (AddMonoidAlgebra.single p 1)))) ∧
    (∃ e : (PolynomialLift L S (K × T) n f ⧸ polynomialLiftIdeal L S (K × T) n f) ≃+*
        (PolynomialRing L (K × T) n ⧸ Ideal.map (polynomialChartMap L n f) (completionIdeal L S n)),
      ∀ b : PolynomialRing L (K × T) n,
        e (Ideal.Quotient.mk _ (polynomialLiftRight L S (K × T) n f b)) = Ideal.Quotient.mk _ b) ∧
    (∀ (N : PrimeSpectrum (PolynomialLift L S (K × T) n f)),
      Ideal.map (polynomialLiftRight L S (K × T) n f)
        (polynomialParameterIdeal L (K × T) n ⊔ polynomialStratumIdeal L K T n) ≤ N.asIdeal →
      ∀ (p : PrimeSpectrum (PolynomialRing L K n)) (r : PrimeSpectrum (PolynomialRing L (K × T) n)),
      p.asIdeal = Ideal.comap ((polynomialLiftRight L S (K × T) n f).comp
        (polynomialChartMap L n (AddMonoidHom.inl K T))) N.asIdeal →
      ∀ hr : r.asIdeal = Ideal.comap (polynomialLiftRight L S (K × T) n f) N.asIdeal,
        polynomialParameterIdeal L K n ≤ p.asIdeal ∧
        r.asIdeal = Ideal.map (polynomialChartMap L n (AddMonoidHom.inl K T)) p.asIdeal ⊔
          polynomialStratumIdeal L K T n ∧
        Ideal.map (polynomialChartMap L n f) (completionIdeal L S n) ≤ r.asIdeal ∧
        polynomialLiftIdeal L S (K × T) n f ≤ N.asIdeal ∧
        (∀ N' : PrimeSpectrum (PolynomialLift L S (K × T) n f),
          Ideal.comap (polynomialLiftRight L S (K × T) n f) N'.asIdeal = r.asIdeal →
          polynomialLiftIdeal L S (K × T) n f ≤ N'.asIdeal → N' = N) ∧
        (∃ e : N.asIdeal.ResidueField ≃+* r.asIdeal.ResidueField,
          e.symm.toRingHom = Ideal.ResidueField.map r.asIdeal N.asIdeal
            (polynomialLiftRight L S (K × T) n f) hr) ∧
        (∃ e : r.asIdeal.ResidueField ≃+* FractionRing (PolynomialRing L K n ⧸ p.asIdeal),
          ∀ a : PolynomialRing L K n,
            e (algebraMap (PolynomialRing L (K × T) n) r.asIdeal.ResidueField
              (polynomialChartMap L n (AddMonoidHom.inl K T) a)) =
            algebraMap (PolynomialRing L K n ⧸ p.asIdeal)
              (FractionRing (PolynomialRing L K n ⧸ p.asIdeal)) (Ideal.Quotient.mk _ a)) ∧
        (∀ (p₀ : ℕ), IsCohenRing p₀ L → ∀ θ : Complete L S n,
          θ - (p₀ : Complete L S n) ∈ completedChartIdeal L S n →
          polynomialLiftLeft L S (K × T) n f θ ∈ N.asIdeal ∧
          HasCompatibleQuotientResidueField (PolynomialLift L S (K × T) n f) N
            (polynomialLiftLeft L S (K × T) n f θ))) := by
  sorry

end ToricMonoid
