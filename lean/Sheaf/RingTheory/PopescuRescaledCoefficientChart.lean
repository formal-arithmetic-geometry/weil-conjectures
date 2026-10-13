/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
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
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.RegularRingSmoothAscent
import Sheaf.RingTheory.RegularSequencePolynomialVariables
import Sheaf.RingTheory.RegularSequencePowers

/-!
# Simultaneous rescaling of an existing Artinian coefficient chart

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, steps 10--13, 15, 23 and 25.
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

/-- Rescale a given flat polynomial chart and its Artinian coefficient solution. This is
only the simultaneous rescaling and coefficient inclusion step, before taking c-th powers
of the parameter list or constructing the polynomial evaluation algebra homomorphism.
Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, steps 10--13, 15, 23 and 25.
(blueprint: lem-weil-pbc-popescu-rescaled-coefficient-chart).

Proof: The flat local map ψ₀, whose maximal ideal extends to that of L, has zero-dimensional
closed fibre. The flat height formula and regularity give a regular system of d parameters
in its source and in L. Choose polynomial representatives, clearing their denominators.
Their permutations are regular. Adjoin d variables t_i and send X_i to u_i t_i. Apply
regular-sequence powers and Ogoma successively on the quotients by preceding (8c)-th
powers, multiplying each u_i by an element outside the contracted prime. Previously
established equalities and the parameter ideals do not change.

The images of the generators f(X_i) are in D₀. Since f is surjective and the local flat
map g₀ is injective, α modulo the maximal-ideal power factors as a k-algebra map into D₀.
At each next parameter, faithful-flat contraction writes u_i^N as a linear combination
of the images of a_j in the current coefficient ring. Lift the coefficients to L.
The error lies in m_L^(N+d(8c)), which is contained in m_L^(d(8c)) times the singular
ideal. Correct this error, then multiply by u_i^N. The correction terms vanish modulo
the chosen maximal-ideal power, preserving coefficient membership.

For the resulting coefficients w_j in L, choose s₀ outside q and v_j in Λ with
w_j=v_j/s₀. Choose s₁ outside q annihilating s₀u_i^(2N)-sum v_j α(a_j).
Put s=s₀s₁ and μ_j=s^(2N-1)s₁v_j. Then (su_i)^(2N)=sum μ_j α(a_j)
and μ_j/s^(2N)=w_j. Enlarge the coefficient ring by 07FI so a positive power of s
belongs to it, replacing μ_j by the corresponding rescaled coefficients. Apply Ogoma
on Λ modulo preceding parameter powers, and use 07FI again to include a suitable
positive power of the new clearing unit. This gives δ_i outside q and ell(i,j), with
both their residue classes in the enlarged coefficient ring. Induct on i; extensions
preserve all previously included elements and equations.

Append zero to the unpowered list and map t_i to δ_i in Λ. Set K=m_L^(N+d(8c))
and I₀ to the extension of the initial contracted prime power to R. Since the t_i
are units at q∩R, the pigeonhole bound for d generators proves the three required
containments. For d=0 the maximal ideals vanish and N>0 handles the zero ideal powers.

Give E=D'[t_i] its R/I₀-algebra structure using the coefficient map on the old
variables and t_i↦t_i. Localization, polynomial base change and composition show
it essentially smooth. Its evaluation at the coefficient representatives δ_i is
compatible with R because it agrees on every old variable and each t_i. The local
flat map g is retained, as are the images of A, ell and the unscaled u_i. The δ_i
are units because g is local and their images lie outside the maximal ideal.
Finally present the essentially smooth coefficient algebras by finite polynomial
algebras over k and their localizations, transporting these constructions to
Type(max u v); reindex the finite old and added variables by Fin m. These transports
preserve the displayed ring-homomorphism equalities and scalar towers. -/
theorem exists_popescu_rescaled_coefficient_chart
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
    (c : ℕ) (hc : 0 < c)
    (r : ℕ) (f : MvPolynomial (Fin r) k →ₐ[k] A) (hf : Function.Surjective f)
    (m₀ : ℕ) (φ₀ : MvPolynomial (Fin m₀) k →ₐ[k] Λ)
    (ψ₀ : Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) →+*
      Localization.AtPrime q.asIdeal)
    (hψ₀ : ψ₀.comp (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom))) =
      (algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom)
    (hideal₀ : q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal)) =
      (q.asIdeal.comap φ₀.toRingHom).map
        ((algebraMap Λ (Localization.AtPrime q.asIdeal)).comp φ₀.toRingHom))
    (hflat₀ : ψ₀.Flat)
    (D₀ : Type (max u w)) [CommRing D₀] [IsLocalRing D₀] [IsArtinianRing D₀]
    [Algebra (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^ (N + d * (8 * c))) D₀]
    (g₀ : D₀ →+* Localization.AtPrime q.asIdeal ⧸
      (q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        (N + d * (8 * c)))
    [IsLocalHom (algebraMap (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
      ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
          (N + d * (8 * c))) D₀)]
    [IsLocalHom g₀]
    (hsmooth₀ : EssentiallySmooth
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c))) D₀)
    (hgflat₀ : g₀.Flat)
    (hfactor₀ : (g₀.comp (algebraMap
      (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom) ⧸
        ((q.asIdeal.comap φ₀.toRingHom).map (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c))) D₀)).comp
      (Ideal.Quotient.mk (((q.asIdeal.comap φ₀.toRingHom).map
        (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)))) ^
            (N + d * (8 * c)))) =
      (Ideal.Quotient.mk ((q.asIdeal.map
        (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
          (N + d * (8 * c)))).comp ψ₀)
    (hinc₀ : ∀ i : Fin r, Ideal.Quotient.mk
      ((q.asIdeal.map (algebraMap Λ (Localization.AtPrime q.asIdeal))) ^
        (N + d * (8 * c)))
      (algebraMap Λ (Localization.AtPrime q.asIdeal) (α (f (MvPolynomial.X i)))) ∈
        Set.range g₀) :
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
        π i = algebraMap S (MvPolynomial (Fin m) k) (MvPolynomial.X j)) ∧
      (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (π i) ∈ q.asIdeal) ∧
      (∀ (i : Fin (d + 1))
        (x : MvPolynomial (Fin m) k ⧸ Ideal.span
          {y | ∃ j : Fin (d + 1), j.val < i.val ∧ y = π j ^ (c * 8)}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
      (∀ (i : Fin (d + 1))
        (x : Λ ⧸ Ideal.span
          {y | ∃ j : Fin (d + 1), j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (π j) ^ (c * 8)}),
        π i • x = 0 ↔ π i ^ 2 • x = 0) ∧
    let R := MvPolynomial (Fin m) k
    let J := Ideal.span (Set.range (fun i : Fin (d + 1) ↦ π i ^ (c * 8)))
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    letI := Localization.AtPrime.algebraOfLiesOver (q.asIdeal.under R) q.asIdeal
    let JQ := J.map (algebraMap R Q)
    let JL := (J.map (algebraMap R Λ)).map (algebraMap Λ L)
    ∃ (n : ℕ), 0 < n ∧ IsLocalRing.maximalIdeal L ^ n ≤ JL ∧
      ∃ (I₀ : Ideal R) (K : Ideal L),
        I₀.map (algebraMap R Q) ≤ JQ ∧ K ≤ JL ∧
        (I₀.map (algebraMap R Q)).map (algebraMap Q L) ≤ K ∧
        ∃ (D' : Type (max u v)) (_ : CommRing D')
          (_ : IsLocalRing D') (_ : IsArtinianRing D') (_ : Algebra k D'),
          let E := MvPolynomial (Fin d) D'
          ∃ (_ : Algebra R E) (_ : Algebra (R ⧸ I₀) E)
            (_ : IsScalarTower R (R ⧸ I₀) E)
            (algSE : Algebra S E) (_ : IsScalarTower S R E)
            (_ : Algebra k E) (_ : IsScalarTower k S E),
            EssentiallySmooth (R ⧸ I₀) E ∧
            ∃ (_ : IsScalarTower k D' E)
              (f₀ : A →ₐ[k] D') (g : D' →+* L ⧸ K)
              (u₀ : Fin d → D') (δ : Fin d → D'ˣ) (coeff : Fin d × Fin s → D'),
              IsLocalRing (L ⧸ K) ∧ IsLocalHom g ∧ g.Flat ∧
              (∀ i : Fin d, @algebraMap S E _ _ algSE (MvPolynomial.X (R := k) i) =
                MvPolynomial.C (σ := Fin d) (u₀ i) * MvPolynomial.X (R := D') i) ∧
              (∀ z : R, MvPolynomial.eval₂Hom g (fun i ↦ g (δ i : D'))
                (algebraMap R E z) =
                Ideal.Quotient.mk K (algebraMap Λ L (algebraMap R Λ z))) ∧
              (∀ x, g (f₀ x) =
                Ideal.Quotient.mk K (algebraMap Λ L (α x))) ∧
              (∀ ij, g (coeff ij) =
                Ideal.Quotient.mk K (algebraMap Λ L (ell ij))) := by sorry

end Algebra
