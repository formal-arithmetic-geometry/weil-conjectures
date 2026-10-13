/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
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

/-- Construct the rescaled coefficient algebra before padding the parameter list and
comparing powers of its parameter ideals. Source: Stacks Project, Smoothing Ring Maps,
Lemma 07FJ, steps 10--13, 15 and 25.
(blueprint: lem-weil-pbc-popescu-unpadded-coefficient-chart).

Proof: The source of the flat local chart is regular of dimension d, by smooth ascent
from the field and the flat height formula with zero-dimensional closed fibre. Choose
d polynomial representatives of a regular system of parameters. Their images generate
the maximal ideal of L, since the original contracted prime extends to that ideal.
Adjoin d polynomial variables t_i and put rho_i = u_i t_i. Apply Ogoma successively
on the quotients by preceding (8c)-th powers, using regularity of permutations and powers
after localization. This rescales u_i by units of the original prime localization and
produces the first kernel equalities without changing the parameter ideal.

The map g₀ is faithfully flat and injective. The generator inclusions and the
surjective presentation f therefore lift α modulo the maximal-ideal power to D₀.
Induct on the parameters. Faithful-flat ideal contraction writes u_i^N as a linear
combination of the singular-ideal generators in the current coefficient algebra.
Lift the coefficients d_j to c_j in L. The error epsilon lies in m_L^n, where
n=N+d(8c), and m_L^n is contained in m_L^(n-N) times the singular ideal.
Write epsilon=sum a_j c'_j with c'_j in m_L^(n-N). Multiplying by u_i^N gives
u_i^(2N)=sum a_j w_j, with w_j=u_i^N(c_j+c'_j). The correction u_i^N c'_j
vanishes modulo m_L^n, so every w_j has residue in the coefficient algebra.
Choose s₀ outside q and v_j in Λ with w_j=v_j/s₀. Choose s₁ outside q
annihilating s₀u_i^(2N)-sum v_j α(a_j), and set s=s₀s₁ and
μ_j=s^(2N-1)s₁v_j. Then (su_i)^(2N)=sum μ_j α(a_j) in Λ and
μ_j/s^(2N)=w_j in L. Apply 07FI to include a positive power of s,
replacing s and μ_j by the correspondingly rescaled expressions. Apply Ogoma
on Λ modulo preceding parameter powers, and apply 07FI again to include a power of
its clearing factor. This yields δ_i outside q and ell(i,j), all with residue classes
in the enlarged Artinian coefficient algebra. Extensions preserve earlier equations.

Evaluate t_i at δ_i. Let H be the extension to R of the initial contracted prime.
The t_i become units in Q, so rho_i generate HQ; their images generate the maximal
ideal of L. Use K=m_L^(N+d(8c)) and I₀=H^(N+d(8c)). Locality makes the included δ_i
units. Polynomial base change of the essentially smooth coefficient algebra gives
E and its R/I₀-algebra structure. Composition with the original localization is
essentially smooth. The structural and evaluation maps agree on coefficients and
all old and added variables. Retain the lifted A-map, parameters and coefficients.
Finally transport the essentially finite type coefficient algebra to Type(max u v)
using its finite presentation and localization, and reindex the finite polynomial
variables as Fin m. For d=0 the parameter ideals are zero; the same constructions
use no added variables or rescaling steps. No padding or powered-ideal containment
is included in this statement. -/
theorem exists_popescu_unpadded_coefficient_chart
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
    let R := MvPolynomial (Fin m) k
    let Q := Localization.AtPrime (q.asIdeal.under R)
    let L := Localization.AtPrime q.asIdeal
    let K := IsLocalRing.maximalIdeal L ^ (N + d * (8 * c))
    ∃ (H : Ideal R),
      H.map (algebraMap R Q) =
        Ideal.span (Set.range (fun i : Fin d ↦ algebraMap R Q (rho i))) ∧
      H.map ((algebraMap Λ L).comp (algebraMap R Λ)) = IsLocalRing.maximalIdeal L ∧
      ∃ (D' : Type (max u v)) (_ : CommRing D')
        (_ : IsLocalRing D') (_ : IsArtinianRing D') (_ : Algebra k D'),
        let I₀ := H ^ (N + d * (8 * c))
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
            (∀ x, g (f₀ x) = Ideal.Quotient.mk K (algebraMap Λ L (α x))) ∧
            (∀ ij, g (coeff ij) = Ideal.Quotient.mk K (algebraMap Λ L (ell ij))) := by sorry

end Algebra
