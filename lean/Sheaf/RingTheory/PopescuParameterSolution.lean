/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.RingTheory.GRing
public import Sheaf.RingTheory.PopescuResolution
public import Sheaf.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Defs

/-!
# Parameters and coefficient solutions for the explicit standardizer

Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ,
items item-NP through item-choose-deltai and item-eighth-resolve.
-/

@[expose] public section

universe u v w
namespace Algebra

/-- Choose parameters and a coefficient solution for the explicitly presented
standardizer. No improved presentation C₀ is an input or an output; the conclusion
concerns B itself and thus can be combined with any improved presentation retracting
onto B.
Source: Stacks Project, Smoothing Ring Maps, proof of Lemma 07FJ,
items item-NP, item-choose-pii, item-modify-pii, item-choose-deltai,
item-set-map-R, item-sixth-resolve, item-eighth-resolve, and item-done.
(blueprint: lem-weil-pbc-popescu-parameter-solution).

Proof: Put L = Λ_q and d = dim L; geometric regularity makes L regular, so d is
also the minimal number of generators of its maximal ideal, the supplied hd.
Set e = 8c and n = N + de. Apply 07FH to the images of finite algebra generators
of A modulo m_L^n. This gives a polynomial base k[y], its prime p, a flat local
map P₀ = k[y]_p → L with pL = m_L, and an essentially smooth local Artinian
solution D₀ over P₀/p^n, flat locally over L/m_L^n. The last map is faithfully
flat and injective, so the generator images define A → D₀. The flat height
formula identifies dim P₀ with d. Choose parameters u_i in p generating the
maximal ideals of P₀ and L. Put R = k[y,t_0,...,t_(d-1)] and map k[x] to R by
X_i ↦ u_i t_i. Apply Ogoma successively to the modules R/((u_jt_j)^e:j<i),
rescaling u_i by elements outside p, to equalize the first and square kernels.
For each i, faithful-flat contraction puts u_i^N in (a_j)D₀. Lift coefficients
into L, correct the error in m_L^(n-N), and multiply by u_i^N to obtain
u_i^(2N) = sum_j a_j w_j with the correct images modulo m_L^n. Clear the finitely
many denominators, and multiply by a further denominator killing the equality's
error in Λ. This yields (s u_i)^(2N) = sum_j a_j μ_j in Λ. Use 07FI to enlarge D₀
until a positive power of s lies in it, rescaling μ_j. Ogoma on
Λ/((δ_ju_j)^e:j<i) and a second use of 07FI supply δ_i outside q and λ_ij with
(δ_i u_i)^(2N) = sum_j a_j λ_ij, the first/square kernel equality, and both
δ_i and λ_ij in the enlarged coefficient solution D'. Earlier conditions persist.
Map R to Λ by t_i ↦ δ_i. Map B to Λ using its presentation P, taking x_i to
δ_i u_i and z_ij to λ_ij; this respects the displayed relations and agrees with α
on A. Take I₀ = p^nR and K = m_L^n. In Q all t_i are units, so the pigeonhole
bound m_L^(d(e-1)+1) ⊆ (u_i^e)L and its counterpart in P₀ prove the three ideal
containments, since n = N + de is positive. Put E = D'[t]. The map R/I₀ to
(P₀/p^n)[t] is a localization. Polynomial extension of D' is essentially smooth
by base change, and composition makes E essentially smooth over R/I₀.
Map B to E by sending A to its image in D', x_i to u_i t_i and z_ij to
bar(λ_ij)t_i^(2N)bar(δ_i)^(-2N). The δ_i are units because D' → L/K is local;
faithful-flat injectivity checks all relations in D'[t]. Evaluation t_i ↦ δ_i
and the coefficient map D' → L/K give b. These maps agree with B → Λ → L/K
on coefficients and every generator of P. Replace the parameter list (u_it_i)^c
by that list with a final zero. The two kernel equalities persist for positive
powers by induction, and the appended zero contributes no generator to J.
Finite polynomial models for the smooth coefficient algebras and their
localizations give D' in Type(max u v), independently of w. Identify R with a
polynomial algebra on Fin m by reindexing its finitely many variables. For d = 0,
m_L = 0, n = N, J = 0 and the same construction and containments apply. -/
theorem exists_popescu_parameter_solution
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
    (B : Type (max u v)) [CommRing B] [Algebra k B] [Algebra A B]
    [IsScalarTower k A B] [Algebra (MvPolynomial (Fin d) k) B]
    [IsScalarTower k (MvPolynomial (Fin d) k) B]
    (P : Presentation A B (Fin d ⊕ (Fin d × Fin s)) (Fin d))
    (hval : ∀ i, P.val (Sum.inl i) =
      algebraMap (MvPolynomial (Fin d) k) B (MvPolynomial.X i))
    (hrel : ∀ i, P.relation i =
      (MvPolynomial.X (Sum.inl i) ^ (2 * N) -
        ∑ j : Fin s, MvPolynomial.X (Sum.inr (i, j)) * MvPolynomial.C (a j) :
          MvPolynomial (Fin d ⊕ (Fin d × Fin s)) A))
    (c : ℕ) (hc : 0 < c) :
    let S := MvPolynomial (Fin d) k
    ∃ (m : ℕ) (_ : Algebra (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k (MvPolynomial (Fin m) k) Λ)
      (_ : Algebra S (MvPolynomial (Fin m) k))
      (_ : IsScalarTower k S (MvPolynomial (Fin m) k))
      (_ : Algebra S Λ) (_ : IsScalarTower S (MvPolynomial (Fin m) k) Λ)
      (_ : IsScalarTower k S Λ)
      (η : B →ₐ[S] Λ) (π : Fin (d + 1) → MvPolynomial (Fin m) k),
      (η.restrictScalars k).comp (IsScalarTower.toAlgHom k A B) = α ∧
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
            (_ : Algebra S E) (_ : IsScalarTower S R E),
            EssentiallySmooth (R ⧸ I₀) E ∧
            ∃ (θ : B →ₐ[S] E) (b : E →ₐ[R] L ⧸ K),
              (b.restrictScalars S).comp θ =
                ((Ideal.Quotient.mkₐ R K).restrictScalars S).comp
                  ((IsScalarTower.toAlgHom S Λ L).comp η) := by sorry

end Algebra
