module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.CategoryTheory.ObjectProperty.Ind
public import Mathlib.RingTheory.Smooth.Basic
public import Sheaf.RingTheory.PopescuLifting
public import Sheaf.RingTheory.SingularIdeal

@[expose] public section

universe u v
open CategoryTheory
open scoped nonZeroDivisors

/-- Auxiliary output of the Popescu lifting construction, including pointwise smoothness.

(blueprint: lem-weil-pbc-popescu-smooth-lift-data)

Proof: Construct a finite polynomial presentation and apply `popescu_lifting` as in
Stacks Project Lemma 07F5. Injectivity of multiplication by `π` gives the required
annihilator equalities. The quotient maps give the compatible map modulo `π⁴`.
Clause (b) of the lifting lemma handles primes away from `π`; clause (c), together
with smoothness of the chosen smooth quotient algebra, handles primes over `π`.
Thus the resulting finitely presented algebra is smooth at every prime.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07F5, proof (blueprint:
lem-weil-pbc-popescu-smooth-lift-modulo-eight).
The construction produces a finitely presented algebra, a compatible map modulo π⁴,
and smoothness at every prime; the detailed polynomial construction is the content of
this intermediate assertion. -/
theorem exists_popescu_smooth_lift_data
    (R : Type u) (Λ : Type (max u v)) [CommRing R] [CommRing Λ] [Algebra R Λ]
    [IsNoetherianRing R]
    (A : Type (max u v)) [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A]
    (α : A →ₐ[R] Λ) (π : R) (hπ : π ∈ R⁰) (hπΛ : algebraMap R Λ π ∈ Λ⁰)
    (hmod : ObjectProperty.ind.{max u v}
      (fun B : CommAlgCat.{max u v} (R ⧸ Ideal.span {π ^ 8}) ↦
        Algebra.Smooth (R ⧸ Ideal.span {π ^ 8}) B)
      (CommAlgCat.of (R ⧸ Ideal.span {π ^ 8})
        (Λ ⧸ (Ideal.span {π ^ 8}).map (algebraMap R Λ)))) :
    ∃ (D : Type (max u v)) (_ : CommRing D) (_ : Algebra R D)
      (_ : Algebra.FinitePresentation R D) (δ : D →ₐ[R] Λ),
      (∀ q : PrimeSpectrum D, Algebra.IsSmoothAtPrime R q) ∧
      ∃ φ : (A ⧸ Ideal.span {(algebraMap R A π) ^ 4}) →ₐ[R]
        (D ⧸ Ideal.span {(algebraMap R D π) ^ 4}),
        ∀ (a : A) (d : D),
          φ (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ d →
          Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (α a) =
            Ideal.Quotient.mk (Ideal.span {(algebraMap R Λ π) ^ 4}) (δ d) := by
  sorry
