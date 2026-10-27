module

public import Sheaf.RingTheory.PermissibleBasisChartData
public import Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-! # A single-index correction in a permissible standard basis

Source: Hironaka, Certain numerical characters of singularities (1970),
Lemma 20, pp.176–181, with (13.1) and (19.1)–(19.2).
(blueprint: lem-trf-permissible-standard-basis-one-step).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace Hironaka

open AlgebraicGeometry AlgebraicGeometry.AffineBlowup AlgebraicGeometry.NodalLocal

/-- The single-index assertion of Hironaka's Lemma 20. All indices are shifted down
by one, so `a = 0` is the empty-prefix case. Maps supplied as coordinate realizations
are pinned on every coefficient and variable, rather than chosen arbitrarily.
The prime `z` is the point in the affine chart of the blowup, so its local ring is
`Localization.AtPrime z.asIdeal`. The contraction equation says that it is over
`m = M/b`. The ambient local ring and transform ideal are the recorded canonical
localizations and kernel. `hp` is precisely reduction of its prime modulo `M`.

Source: Hironaka (1970), Lemma 20, pp.176–181.
(blueprint: lem-trf-permissible-standard-basis-one-step).

Proof, following the seven steps of the node:
1. Embed the parameter chart in `T[1/x₀]` using the regular parameter-chart
presentation. For `h ∈ P^e`, expand it in degree-e parameter monomials; dividing
by `x₀^e` gives an element of the chart. Reduction modulo `H = (x₀,y)` is
its dehomogenized degree-e initial form. The quotient chart embeds in `R[1/x₀]`,
so multiplication by `x₀` is injective there and after localization. Hence every
`g_i` maps to zero in the blowup local ring.
2. Set `q_j = g_j-w_j` for `j<a`. They have order `d_j`, lie in the transform
ideal, and reduce to the dehomogenizations of `φ_j`. Projective-order initial
minimality gives their exact orders and minimal initial forms in the fibre local
ring, and the graded quotient sends the initial forms of `q_j` to those forms.
3. Induct on degrees `e<d_a` in the initial transform ideal. The earlier forms
of degree `e` are independent modulo the ideal of smaller-degree forms, by
mapping a relation to the fibre. The assumed initial entries of `ν*` say their
number is the dimension of the indecomposable degree-e space. Thus they form a
basis. Lift coefficients and cancel the finitely many degrees below `d_a` to
obtain `a' ⊆ (q_j:j<a)+M'^d_a`.
4. Reduce the resulting relation for `g_a` modulo `H`. Homogeneous approximation
at precision `d_a` supplies `C_j` of degree `d_a-d_j`, making
`ψ = φ_a-Σ C_j φ_j` belong to `U_d_a`. Minimality makes `ψ` nonzero.
5. Lift coefficients of `C_j` to `T` and form `c_j ∈ P^(d_a-d_j)`. The corrected
original has initial form `ψ` and exact order `d_a`. The chart division formula
gives the displayed corrected divided element and all the required fractions.
6. Apply the normal-flat chart relation-removal lemma to the earlier `q_j`,
using the finite-jet generation of step 3. The corrected divided element reduces
to an element of `N^d_a`, so it differs from an element of `H(q_j:j<a)` by an
element of `M'^d_a`. Triangular induction identifies the q-ideal with the
original earlier g-ideal, giving the required `v`.
7. Projective-order initial minimality for the singleton nonzero `ψ ∈ U_d_a`
gives exact order `d_a` in the fibre local ring. Therefore the last remainder
cannot lie in `M'^(d_a+1)`, establishing its exact order. At the first index,
all sums and earlier ideals are zero and the same argument gives `v = 0`.
-/
theorem permissibleStandardBasisOneStep
    {T : Type u} [CommRing T] [IsRegularLocalRing T]
    (r s : ℕ) (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (b : Ideal T) (hb : b ≤ Ideal.span (Set.range x))
    (hflat : Module.Flat
      ((T ⧸ b) ⧸ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))
      (Ideal.associatedGraded ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))))
    (hred : IsReduced (T ⧸ b))
    (hmin : ∀ q ∈ minimalPrimes (T ⧸ b),
      ¬ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk b) ≤ q)
    (ι : ParameterChart x →+* Localization.Away (x 0)) (hι : IsAmbientChartMap x ι)
    (ρ : ParameterChart x →+*
      chartRing ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))
        (Ideal.Quotient.mk b (x 0))) (hρ : IsQuotientChartMap x b ρ)
    (z : PrimeSpectrum (chartRing ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))
      (Ideal.Quotient.mk b (x 0))))
    (hz : z.asIdeal.comap ((algebraMap (T ⧸ b) _).comp (Ideal.Quotient.mk b)) =
      IsLocalRing.maximalIdeal T)
    [IsRegularLocalRing (LocalChart ρ z)]
    (p : PrimeSpectrum
      (MvPolynomial {i : Fin (r + 1) // i ≠ 0} (IsLocalRing.ResidueField T)))
    (hp : p.asIdeal.comap (residuePolynomialMap (T := T) r) =
      (PrimeSpectrum.comap ρ z).asIdeal.comap
        (Ideal.Quotient.mk (PermissibleCoordinateChart.relations x Finset.univ 0)))
    (χ : MvPolynomial (Fin (r + 1) ⊕ Fin s) (IsLocalRing.ResidueField T) →+*
      Ideal.associatedGraded (IsLocalRing.maximalIdeal T))
    (hχ : IsParameterGradedMap x y χ)
    (m : ℕ) (hm : 1 ≤ m) (f : Fin m → T) (d : Fin m → ℕ)
    (φ : Fin m → MvPolynomial (Fin (r + 1)) (IsLocalRing.ResidueField T))
    (hd : Monotone d) (hdpos : ∀ i, 1 ≤ d i)
    (hf : ∀ i, f i ∈ b ∧ f i ∈ Ideal.span (Set.range x) ^ d i ∧
      adicOrder (IsLocalRing.maximalIdeal T) (f i) = d i)
    (hφ : ∀ i, (φ i).IsHomogeneous (d i) ∧
      ∃ hi : f i ∈ IsLocalRing.maximalIdeal T ^ d i,
        χ (MvPolynomial.rename Sum.inl (φ i)) = initialForm T (d i) ⟨f i, hi⟩)
    (hbasis : IsMinimalGeneratingFamily
      (adicInitialIdeal (IsLocalRing.maximalIdeal T) b)
      (fun i ↦ χ (MvPolynomial.rename Sum.inl (φ i))))
    (g : Fin m → LocalChart ρ z)
    (hg : ∀ i, IsDividedElement x ι (PrimeSpectrum.comap ρ z) (d i) (f i) (g i))
    (a : Fin m)
    (hearlier : ∀ j, j < a → nuStar (transformIdeal ρ z) j.val = d j ∧
      InOrderSpace r p (d j) (φ j) ∧
      ∃ w ∈ exceptionalIdeal x y (PrimeSpectrum.comap ρ z) * prefixIdeal g j,
        adicOrder (IsLocalRing.maximalIdeal (LocalChart ρ z)) (g j - w) = d j)
    (hnext : (d a : ℕ∞) ≤ nuStar (transformIdeal ρ z) a.val) :
    ∃ (c : Fin m → T) (γ : Fin m → LocalChart ρ z) (v : LocalChart ρ z),
      (∀ j, j < a → c j ∈ Ideal.span (Set.range x) ^ (d a - d j) ∧
        IsDividedElement x ι (PrimeSpectrum.comap ρ z) (d a - d j) (c j) (γ j)) ∧
      v ∈ exceptionalIdeal x y (PrimeSpectrum.comap ρ z) * prefixIdeal g a ∧
      adicOrder (IsLocalRing.maximalIdeal T) (correctedGenerator f a c) = d a ∧
      (∃ ψ, InOrderSpace r p (d a) ψ ∧
        ∃ hψ : correctedGenerator f a c ∈ IsLocalRing.maximalIdeal T ^ d a,
          χ (MvPolynomial.rename Sum.inl ψ) =
            initialForm T (d a) ⟨correctedGenerator f a c, hψ⟩) ∧
      IsDividedElement x ι (PrimeSpectrum.comap ρ z) (d a)
        (correctedGenerator f a c) (correctedGenerator g a γ) ∧
      adicOrder (IsLocalRing.maximalIdeal (LocalChart ρ z))
        (correctedGenerator g a γ - v) = d a := by
  sorry

end Hironaka
