/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.RingTheory.GRing
public import Sheaf.RingTheory.PopescuResolution
public import Sheaf.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Defs
import Sheaf.AlgebraicGeometry.Ogoma
import Sheaf.RingTheory.EssentiallySmoothComp
import Sheaf.RingTheory.PopescuEnlargeSolutionModulo
import Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence
import Sheaf.RingTheory.RegularRingSmoothAscent
import Sheaf.RingTheory.RegularSequencePolynomialVariables
import Sheaf.RingTheory.RegularSequencePowers

/-!
# Rescaled parameters and Artinian coefficient lifts

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, steps 10--13, 15
and the coefficient quotient of step 25.
(blueprint: lem-weil-pbc-popescu-coefficient-rescaling).
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

/-- Construct the rescaled parameters and their coefficient lifts, before forming the
polynomial quotient chart. Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ
(`lemma-resolve-general`), items `item-choose-pii`, `item-modify-pii`,
`item-choose-deltai`, and `item-set-map-R`.
(blueprint: lem-weil-pbc-popescu-coefficient-rescaling).

Proof: Geometric regularity makes L regular. Smooth ascent makes P regular, and the
flat local height formula, with closed fibre a field, gives the same dimension d for
P localized at p₀. Choose polynomial representatives uP of a regular system of parameters.
All their permutations are regular. On P[t], regular-sequence powers and Ogoma successively
multiply uP_i by elements outside p₀ to equalize the first and square kernels modulo
preceding (8c)-th powers. Such multiplication preserves parameter generation.
The flat local map g₀ is faithfully flat, hence injective. Lift the finite generators of A
to D₀; their relations vanish by injectivity, giving the retained A-map.
Induct on i. Faithfully flat ideal contraction writes uP_i^N as sum a_j d_j in the
current coefficient ring. Lift the d_j to L; write the error as sum a_j c'_j with
c'_j in m_L^(n-N), n=N+d(8c). Multiplying by uP_i^N kills each correction modulo m_L^n
and gives uP_i^(2N)=sum a_j w_j, with each w_j's residue in the coefficient ring.
For a common denominator s₀ and v_j with w_j=v_j/s₀, choose s₁ outside q annihilating
s₀ uP_i^(2N)-sum v_j a_j. Set s=s₀s₁ and mu_j=s^(2N-1)s₁v_j. Then
(s uP_i)^(2N)=sum mu_j a_j in Λ and mu_j/s^(2N)=w_j in L.
Use 07FI to include a positive power s^r in an essentially smooth coefficient enlargement;
replace s by s^r and mu_j by s^(2N(r-1))mu_j. These preserve both identities.
Apply Ogoma on Λ modulo the preceding rescaled parameter powers. Include a positive power
of its clearing factor by 07FI; its product with s^r is tΛ_i. Rescale mu_j accordingly
to obtain ell(i,j), the Λ kernel equality, and coefficient lifts. All earlier identities
persist under the enlargement. Since g is local, the lifts of tΛ_i are units.
The finite tower is essentially smooth over P_(p₀)/p₀^n and hence over B=P/p₀^n, by
localization and composition. A smooth finite-presentation model over the small B and its
fraction localization are small; transport to Type(max u v) along their algebra equivalence.
Reindex the old and new variables using Fin(m₀+d) to obtain E, and define the displayed
algebra structures by evaluation at tΛ and X_i↦uP_i t_i. When d=0 both inductions are empty;
all parameter and coefficient families are empty and the source parameter ideal is zero.
This theorem does not form H, R/H^n, or its polynomial quotient equivalence. -/
theorem exists_popescu_coefficient_rescaling
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
      (_ : IsScalarTower k S Λ) (ell : Fin d × Fin s → Λ)
      (rho : Fin d → MvPolynomial (Fin m) k),
    (rho = fun i ↦ algebraMap S (MvPolynomial (Fin m) k) (MvPolynomial.X i)) ∧
    (∀ i, algebraMap S Λ (MvPolynomial.X i) ^ (2 * N) =
      ∑ j : Fin s, ell (i, j) * α (a j)) ∧
    (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (rho i) ∈ q.asIdeal) ∧
    (∀ (i : Fin d)
      (x : MvPolynomial (Fin m) k ⧸ Ideal.span
        {y | ∃ j : Fin d, j.val < i.val ∧ y = rho j ^ (c * 8)}),
      rho i • x = 0 ↔ rho i ^ 2 • x = 0) ∧
    (∀ (i : Fin d)
      (x : Λ ⧸ Ideal.span
        {y | ∃ j : Fin d, j.val < i.val ∧
            y = algebraMap (MvPolynomial (Fin m) k) Λ (rho j) ^ (c * 8)}),
      rho i • x = 0 ↔ rho i ^ 2 • x = 0) ∧
    let P := MvPolynomial (Fin m₀) k
    let p₀ := q.asIdeal.comap φ₀.toRingHom
    let B := P ⧸ p₀ ^ (N + d * (8 * c))
    let L := Localization.AtPrime q.asIdeal
    let K := IsLocalRing.maximalIdeal L ^ (N + d * (8 * c))
    ∃ (E : MvPolynomial (Fin m) k ≃ₐ[k] MvPolynomial (Fin d) P)
      (uP : Fin d → P) (tΛ : Fin d → Λ),
      (∀ i, uP i ∈ p₀) ∧
      Ideal.span (Set.range (fun i ↦ algebraMap P (Localization.AtPrime p₀) (uP i))) =
        p₀.map (algebraMap P (Localization.AtPrime p₀)) ∧
      (∀ i, tΛ i ∉ q.asIdeal) ∧
      (∀ i, E (rho i) = MvPolynomial.C (uP i) * MvPolynomial.X i) ∧
      (∀ z : P, algebraMap (MvPolynomial (Fin m) k) Λ (E.symm (MvPolynomial.C z)) =
        φ₀ z) ∧
      (∀ i, algebraMap (MvPolynomial (Fin m) k) Λ (E.symm (MvPolynomial.X i)) = tΛ i) ∧
      ∃ (D : Type (max u v)) (_ : CommRing D) (_ : IsLocalRing D)
        (_ : IsArtinianRing D) (_ : Algebra k D) (_ : Algebra B D)
        (_ : IsScalarTower k B D),
        EssentiallySmooth B D ∧
        ∃ (f₀ : A →ₐ[k] D) (g : D →+* L ⧸ K)
          (δ : Fin d → Dˣ) (coeff : Fin d × Fin s → D),
          IsLocalRing (L ⧸ K) ∧ IsLocalHom g ∧ g.Flat ∧
          (∀ z : P, g (algebraMap B D (Ideal.Quotient.mk (p₀ ^ (N + d * (8 * c))) z)) =
            Ideal.Quotient.mk K (algebraMap Λ L (φ₀ z))) ∧
          (∀ i, g (δ i : D) = Ideal.Quotient.mk K (algebraMap Λ L (tΛ i))) ∧
          (∀ x, g (f₀ x) = Ideal.Quotient.mk K (algebraMap Λ L (α x))) ∧
          (∀ ij, g (coeff ij) = Ideal.Quotient.mk K (algebraMap Λ L (ell ij))) := by sorry

end Algebra
