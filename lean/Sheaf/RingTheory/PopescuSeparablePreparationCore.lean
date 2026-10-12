module

public import Sheaf.RingTheory.PopescuResolution
public import Sheaf.RingTheory.StrictlyStandardElement
public import Mathlib.Algebra.MvPolynomial.Basic
import Sheaf.RingTheory.ImprovePresentation
import Sheaf.RingTheory.SingularIdealLocalizationSmooth
import Sheaf.RingTheory.SmoothFreeDifferentialsStrictlyStandardPower
import Sheaf.RingTheory.SingularIdeal

@[expose] public section

universe u v w

namespace Algebra

/-- The polynomial construction, before choosing parameters in the receiving ring.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FE, first two paragraphs
(blueprint: lem-weil-pbc-popescu-separable-preparation-core).

Proof: choose finite generators a_j of H_{A/k}, since A is Noetherian. Set
R = k[X_i] and B = A[X_i,Z_ij]/(X_i^n - sum_j Z_ij a_j). This is finitely
presented over R. After inverting a_j, eliminate Z_ij for every i; the resulting
polynomial ring over A_(a_j)[X_i] is smooth over R by smooth base change.
After inverting X_i the a_j generate the unit ideal, so smoothness on that principal
cover proves B_(X_i) smooth (if the generator set is empty the localization is zero).
Apply the improve-presentation lemma to B, obtaining a finite-type B-algebra C with
retraction rho : C -> B whose indicated smooth localizations have free differentials.
Since R is Noetherian, C is finitely presented over R. The strict-standard-power lemma
and finiteness of Fin d give a common positive exponent c. The composite A -> B -> C
is beta. All these objects depend only on A, d, n, not on the receiving ring.
For any alpha and phi satisfying the displayed power membership, write
phi(X_i)^n = sum_j lambda_ij alpha(a_j). Evaluation X_i -> phi(X_i),
Z_ij -> lambda_ij defines B -> Lambda, as it kills the relations. Compose with rho
for gamma. Its composite with beta is alpha and it is an R-algebra map.
Smoothness of C_(beta(a_j)) places beta(a_j) in H_{C/R}. Consequently the extension
of H_{A/k} to C lies in H_{C/R}; mapping to Lambda and taking radicals gives the
Popescu-ideal inequality. The quotient and symmetric-algebra constructions use only
carriers in universe max(u,v), so C has the specified universe. -/
theorem exists_popescu_separable_preparation_core
    {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]
    [FinitePresentation k A] (d n : ℕ) (hn : 1 ≤ n) :
    ∃ (c : ℕ) (C : Type (max u v)) (_ : CommRing C) (_ : Algebra k C)
      (_ : Algebra (MvPolynomial (Fin d) k) C)
      (_ : IsScalarTower k (MvPolynomial (Fin d) k) C)
      (_ : FinitePresentation (MvPolynomial (Fin d) k) C) (β : A →ₐ[k] C),
      1 ≤ c ∧
      (∀ i : Fin d, IsStrictlyStandardElement (R := MvPolynomial (Fin d) k)
        (algebraMap (MvPolynomial (Fin d) k) C (MvPolynomial.X i ^ c))) ∧
      ∀ {Λ : Type w} [CommRing Λ] [Algebra k Λ]
        (α : A →ₐ[k] Λ) (φ : MvPolynomial (Fin d) k →ₐ[k] Λ),
        letI := φ.toRingHom.toAlgebra
        (∀ i : Fin d, φ (MvPolynomial.X i) ^ n ∈
          Ideal.map α.toRingHom (singularIdeal k A)) →
        ∃ γ : C →ₐ[MvPolynomial (Fin d) k] Λ,
          (γ.restrictScalars k).comp β = α ∧ popescuIdeal α ≤ popescuIdeal γ := by
  sorry

end Algebra
