/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E3
-/
module

public import Sheaf.RingTheory.GRing
public import Sheaf.RingTheory.PopescuResolution
public import Sheaf.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Defs
import Sheaf.AlgebraicGeometry.Ogoma
import Sheaf.RingTheory.EssentiallySmoothBaseChange
import Sheaf.RingTheory.EssentiallySmoothComp
import Sheaf.RingTheory.PopescuEnlargeSolutionModulo
import Sheaf.RingTheory.PopescuSolutionModulo
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.RegularRingSmoothAscent
import Sheaf.RingTheory.RegularSequencePolynomialVariables
import Sheaf.RingTheory.RegularSequencePowers

/-!
# Coefficient construction for compatible Popescu parameters

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ.
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

/-- Construct the parameters and their coefficient equations, independently of any presented
standardizer algebra. Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ,
items item-NP through item-choose-deltai and item-eighth-resolve.
(blueprint: lem-weil-pbc-popescu-parameter-coefficients).

Proof: Set e = 8c and n = N + de. Apply 07FH to a finite algebra generating family
of A modulo the n-th power of the maximal ideal of L = Λ_q. Its flat local
polynomial model has the same dimension as L by the flat height formula. Since L
is regular, choose d parameters u_i which generate both maximal ideals. Adjoin
variables t_i and let S map by X_i to u_i t_i. Ogoma and regular-sequence powers,
applied successively to the preceding e-th power quotients, permit rescaling the
u_i outside the polynomial prime to give both kernel equalities in the polynomial
ring. Faithful-flat contraction gives coefficients for u_i^N in the singular ideal
inside the Artinian solution. Lift to L, correct modulo the n-th maximal-ideal power,
and multiply by u_i^N. Clear both the coefficient denominators and the equality's
error in Λ, obtaining (δ_i u_i)^(2N) = sum_j λ_ij α(a_j). Use 07FI to include the
clearing units and coefficients in an enlarged Artinian solution. A second Ogoma
application on Λ modulo preceding e-th powers gives the Λ kernel equalities;
further 07FI enlargements preserve all earlier equations.

Map R to Λ by t_i to δ_i, put I₀ = p^n R and K = m_L^n. The t_i become units
in Q. The pigeonhole containment m_L^(d(e-1)+1) ⊆ (u_i^e)L and its polynomial
analogue imply all required containments since n = N + de. The coefficient solution
D' maps faithfully flatly to L/K. Set E = D'[t], whose R/I₀-algebra structure is
essentially smooth by localization, polynomial base change, and composition. Send
A to its coefficient image f in D' and set μ_ij = bar(λ_ij)t_i^(2N)bar(δ_i)^(-2N).
Locality makes bar(δ_i) units; injectivity of D' to L/K proves the displayed
coefficient equations. Evaluation at δ_i defines b and verifies the two image
formulas. Append zero to the list (u_i t_i)^c; equality of first and square kernels
persists under positive powers, so the displayed eighth-power kernel conditions
hold. For d = 0 the maximal ideal is zero and n = N, and these statements remain
valid. Finite polynomial models for D' give its carrier in Type(max u v). Finally
reindex the finite polynomial variables to Fin m and transport all structures. -/
theorem exists_popescu_parameter_coefficients
    {k : Type u} {A : Type v} {Λ : Type w}
    [Field k] [CommRing A] [CommRing Λ] [Algebra k A] [Algebra k Λ]
    [FinitePresentation k A] [IsNoetherianRing Λ]
    (p : ℕ) [CharP k p] (hp : 0 < p)
    (α : A →ₐ[k] Λ) (q : PrimeSpectrum Λ)
    (hreg : IsGeometricallyRegular k Λ)
    (N : ℕ) (hN : 0 < N)
    (hpower : IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal) ^ N ≤
      (Ideal.map α.toRingHom (singularIdeal k A)).map
        (algebraMap Λ (Localization.AtPrime q.asIdeal)))
    (d : ℕ) (hd : d =
      (IsLocalRing.maximalIdeal (Localization.AtPrime q.asIdeal)).spanFinrank)
    (s : ℕ) (a : Fin s → A) (ha : Ideal.span (Set.range a) = singularIdeal k A)
    (c : ℕ) (hc : 0 < c) :
    let S := MvPolynomial (Fin d) k
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (_ : Algebra S (MvPolynomial (Fin m) k))
      (_ : IsScalarTower k S (MvPolynomial (Fin m) k))
      (_ : Algebra S Λ) (_ : IsScalarTower S (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k S Λ)
      (ell : Fin d × Fin s → Λ) (π : Fin (d + 1) → MvPolynomial (Fin m) k),
      (∀ i, algebraMap S Λ (MvPolynomial.X i) ^ (2 * N) =
        ∑ j : Fin s, ell (i, j) * α (a j)) ∧
      (∀ i, π i = 0 ∨ ∃ j : Fin d,
        π i = algebraMap S (MvPolynomial (Fin m) k) (MvPolynomial.X j ^ c)) ∧
      (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
      (∀ (i : Fin (d + 1))
        (x : MvPolynomial (Fin m) k ⧸ Ideal.span
          {y | ∃ j : Fin (d + 1), j.val < i.val ∧ y = π j ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ (i : Fin (d + 1))
        (x : Λ ⧸ Ideal.span
          {y | ∃ j : Fin (d + 1), j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ 8}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin (d + 1) ↦ π i ^ 8))
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let JQ := J.map (algebraMap R Q)
    let JL := (J.map (algebraMap R Λ)).map (algebraMap Λ L)
    ∃ (n : ℕ), 0 < n ∧ IsLocalRing.maximalIdeal L ^ n ≤ JL ∧
      ∃ (I₀ : Ideal R) (K : Ideal L),
        I₀.map (algebraMap R Q) ≤ JQ ∧ K ≤ JL ∧
        (I₀.map (algebraMap R Q)).map (algebraMap Q L) ≤ K ∧
        ∃ (t : ℕ) (D' : Type (max u v)) (_ : CommRing D')
          (_ : IsLocalRing D') (_ : IsArtinianRing D'),
          let E := MvPolynomial (Fin t) D'
          ∃ (_ : Algebra R E) (_ : Algebra (R ⧸ I₀) E)
            (_ : IsScalarTower R (R ⧸ I₀) E)
            (_ : Algebra S E) (_ : IsScalarTower S R E)
            (_ : Algebra k E) (_ : IsScalarTower k S E),
            EssentiallySmooth (R ⧸ I₀) E ∧
            ∃ (f : A →ₐ[k] E) (μ : Fin d × Fin s → E)
              (b : E →ₐ[R] L ⧸ K),
              (∀ i, algebraMap S E (MvPolynomial.X i) ^ (2 * N) =
                ∑ j : Fin s, μ (i, j) * f (a j)) ∧
              (∀ x, b (f x) = Ideal.Quotient.mk K (algebraMap Λ L (α x))) ∧
              (∀ ij, b (μ ij) = Ideal.Quotient.mk K (algebraMap Λ L (ell ij))) := by sorry

end Algebra
