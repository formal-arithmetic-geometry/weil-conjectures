/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Sheaf.RingTheory.GRing
public import Sheaf.RingTheory.PopescuResolution
public import Sheaf.RingTheory.EssentiallySmooth
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Artinian.Defs
public import Mathlib.RingTheory.Regular.RegularSequence
import Sheaf.RingTheory.PopescuEnlargeSolutionModulo
import Sheaf.RingTheory.EssentiallySmoothComp
import Sheaf.RingTheory.RegularSequencePowers
import Sheaf.AlgebraicGeometry.Ogoma

/-!
# Coefficient enlargement along fixed parameters

Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ, item-choose-deltai.
(blueprint: lem-weil-pbc-popescu-coefficient-induction).
-/

@[expose] public section

set_option autoImplicit false

universe u v w
namespace Algebra

/-- Rescale fixed polynomial parameters in Lambda while retaining an Artinian coefficient
solution. Source: Stacks Project, Smoothing Ring Maps, Lemma 07FJ,
`item-choose-deltai`, together with localization and the coefficient descent in item 25.
(blueprint: lem-weil-pbc-popescu-coefficient-induction).

Proof: A flat local map of local rings is faithfully flat and injective. Lift the
finite presentation generators of A to D0 using hinc0. Injectivity checks the relations
and their scalar compatibility, so they give a k-algebra map A to D0. Set n=N+d(8c).
Induct on i, retaining a local essentially smooth coefficient enlargement and all
previous rescaling factors, coefficients, and Lambda kernel equalities. The image of
uP_i^N lies in the extended singular ideal by hpower. Faithful-flat ideal contraction
writes its residue as sum a_j d_j in the current coefficient ring. Lift d_j to L.
The error lies in m_L^n, contained in m_L^(n-N) times the singular ideal. Thus write
the error as sum a_j c'_j with c'_j in m_L^(n-N). Multiplication by uP_i^N kills
these corrections modulo m_L^n. Set w_j=uP_i^N*(c_j+c'_j); then
uP_i^(2N)=sum w_j*a_j exactly in L, and the residue of w_j is the product
of the coefficient-ring image of uP_i^N with d_j, hence belongs to that image.

Choose a common denominator s0 outside q for these coefficients, and a second factor
s1 outside q annihilating the cleared relation's error. Put s=s0*s1 and
mu_j=s^(2N-1)*s1*v_j when w_j=v_j/s0. Then (s*uP_i)^(2N)=sum mu_j*a_j in
Lambda and mu_j/s^(2N)=w_j in L. Apply 07FI to include a positive power s^r in an
essentially smooth enlargement. Replace mu_j by s^(2N*(r-1))*mu_j and s by s^r;
the relation and coefficient residues are preserved. Regular-sequence powers applied
to hsequence give zero kernels after localization modulo preceding parameter powers.
Ogoma supplies a new clearing factor, all positive powers of which equalize the two
kernels in Lambda. Use 07FI again to include one such power in the coefficient ring,
and multiply the rescaling factor and coefficients by this power and its 2N-th power.
Previous claims persist because only the new index is changed and coefficient maps
remain injective. Locality makes lifts of all rescaling factors units.

Compose the finite coefficient tower with the localization of B at the complement of
p0, obtaining essential smoothness over B. To fit Type(max u v), present its smooth
finite-presentation model over B and realize it as a quotient of a finite polynomial
ring over B, then localize at the contracted maximal ideal. This ring has the required
universe, and the equivalence with the original coefficient ring transports all maps
and identities. The case d=0 has no induction steps: retain D0, construct the A-map,
and perform the same small-model replacement. No polynomial reindexing or polynomial
kernel conclusion is asserted. -/
theorem exists_popescu_coefficient_induction
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
    (d : ℕ)
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
        Set.range g₀)
    (uP : Fin d → MvPolynomial (Fin m₀) k)
    (huP : ∀ i, uP i ∈ q.asIdeal.comap φ₀.toRingHom)
    (hspan : Ideal.span (Set.range (fun i ↦
      algebraMap (MvPolynomial (Fin m₀) k)
        (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom)) (uP i))) =
      (q.asIdeal.comap φ₀.toRingHom).map
        (algebraMap (MvPolynomial (Fin m₀) k)
          (Localization.AtPrime (q.asIdeal.comap φ₀.toRingHom))))
    (hsequence : RingTheory.Sequence.IsRegular (Localization.AtPrime q.asIdeal)
      (List.ofFn (fun i ↦ algebraMap Λ (Localization.AtPrime q.asIdeal) (φ₀ (uP i))))) :
    let P := MvPolynomial (Fin m₀) k
    let p₀ := q.asIdeal.comap φ₀.toRingHom
    let B := P ⧸ p₀ ^ (N + d * (8 * c))
    let L := Localization.AtPrime q.asIdeal
    let K := IsLocalRing.maximalIdeal L ^ (N + d * (8 * c))
    ∃ (tΛ : Fin d → Λ) (ell : Fin d × Fin s → Λ),
      (∀ i, tΛ i ∉ q.asIdeal) ∧
      (∀ i, (φ₀ (uP i) * tΛ i) ^ (2 * N) =
        ∑ j : Fin s, ell (i, j) * α (a j)) ∧
      (∀ (i : Fin d)
        (x : Λ ⧸ Ideal.span {y | ∃ j : Fin d, j.val < i.val ∧
          y = (φ₀ (uP j) * tΛ j) ^ (c * 8)}),
        (φ₀ (uP i) * tΛ i) • x = 0 ↔ (φ₀ (uP i) * tΛ i) ^ 2 • x = 0) ∧
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
