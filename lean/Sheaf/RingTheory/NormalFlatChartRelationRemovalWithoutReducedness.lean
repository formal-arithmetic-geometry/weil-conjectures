module

public import Sheaf.RingTheory.PermissibleBasisChartData
public import Sheaf.RingTheory.ProjectiveConeHilbertStandardDegrees
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic

/-! # Removing exceptional-fibre relations without reducedness

Source: Hironaka, Certain numerical characters of singularities (1970),
proof of Lemma 20, (20.3)–(20.12), pp.177–181.
(blueprint: lem-per-normal-flat-chart-relation-removal).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

namespace Hironaka

open AlgebraicGeometry AlgebraicGeometry.AffineBlowup

/-- The finite-jet ideal intersection used in the standard-basis correction.
The natural-number threshold is named `e`; the prefix length is `a.val`, so
`a = 0` includes the empty prefix. Coordinate maps are pinned on coefficients
and variables by the recorded predicates, and all divisions are performed in
`T[1/x₀]` before localization. The chart prime `z` denotes the corresponding
point of the affine open of the blowup. Its local ring is the localization of
that chart at `z`; `transformIdeal` is the kernel of the actual localized map.
No reducedness is assumed on `T ⧸ b`; injectivity of multiplication by the
exceptional coordinate is used only in the chart subring of its localization.
The residue prime equation `hp` identifies the quotient by the old maximal
ideal. The cone fibre `S = G ⊗[A] k` is determined by these rings and maps.
The initial form of `f_i` is written out as its class in the degree-`d_i`
summand `M^(d_i)/M^(d_i+1)` of the associated graded ring.

Source: Hironaka (1970), proof of Lemma 20, (20.3)–(20.12), pp.177–181.
(blueprint: lem-per-normal-flat-chart-relation-removal).

Proof, following the five steps of the node:
1. Expand each element of `P^h` in degree-h parameter monomials and divide by
`x₀^h` in the ambient chart. Its residue modulo `H` is the dehomogenized
initial form. The quotient chart is a subalgebra of `R[1/x₀]`, where `x₀` is
invertible, so an element of the original ideal remains zero after division.
Thus every `g_i` belongs to the transform ideal. Triangular induction on
`q_j = g_j-w_j` gives equality of the earlier q- and g-ideals, `w_j ∈ HJ`,
and the required residues of `q_j`. The quotient maximal ideal is `N`, and
members of its powers lift into the corresponding powers of `M'`.
2. Lift a homogeneous syzygy of total degree h among the earlier initial
forms to coefficients in `P^(h-d_j)`. Its evaluation on the original `f_j`
lies in the original ideal, in `P^h`, and in `M^(h+1)`. Apply
lem-trf-normal-flat-initial-coefficient-lifting to obtain coefficients in
`M P^(h-d_i)`, with remainder in the original ideal intersected with
`P^(h+1)`. Division by `x₀^h` then lies in `H` times the transform ideal.
3. For `z ∈ J ∩ (H+M'^e)`, express `z = Σ h_j q_j`. Induct on stages
`1 ≤ v < e`, maintaining residues of the coefficients in `N^max(v-d_j,0)`.
Their weighted leading sum vanishes modulo `N^(v+1)`. On the active indices
`d_j ≤ v`, lem-trf-projective-order-leading-syzygies expresses this relation
as a finite sum of dehomogenized homogeneous syzygies, up to the next power.
4. Lift their coefficients and subtract these lifted relations. By step 2,
the represented element changes by an element of `H` times the transform
ideal. The finite-jet condition places this in `HJ+M'^(e+1)`. The active
coefficient orders increase, the inactive ones already meet the next bound,
and the represented element remains in `H+M'^e` modulo `HJ+M'^e`.
5. After the finitely many stages, lift the coefficient residues into
`M'^max(e-d_j,0)`. Their differences are in `H`, and multiplication by the
`q_j` of exact order `d_j` puts the lifted sum in `M'^e`. Therefore the
original element is in `HJ+M'^e`. For an empty prefix `J=0`; for `e=1`
there are no induction stages and the positive orders give the conclusion.
-/
theorem normalFlatChartRelationRemovalWithoutReducedness
    {T : Type u} [CommRing T] [IsRegularLocalRing T]
    (r s : ℕ) (x : Fin (r + 1) → T) (y : Fin s → T)
    (hparams : IsLocalRing.IsRegularSystemOfParameters (List.ofFn x ++ List.ofFn y))
    (b : Ideal T) (hb : b ≤ Ideal.span (Set.range x))
    (hflat : Module.Flat
      ((T ⧸ b) ⧸ (Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))
      (Ideal.associatedGraded ((Ideal.span (Set.range x)).map (Ideal.Quotient.mk b))))
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
        χ (MvPolynomial.rename Sum.inl (φ i)) =
          DirectSum.of (Ideal.associatedGradedPiece (IsLocalRing.maximalIdeal T)) (d i)
            (Submodule.Quotient.mk ⟨f i, hi⟩))
    (hbasis : IsMinimalGeneratingFamily
      (adicInitialIdeal (IsLocalRing.maximalIdeal T) b)
      (fun i ↦ χ (MvPolynomial.rename Sum.inl (φ i))))
    (g : Fin m → LocalChart ρ z)
    (hg : ∀ i, IsDividedElement x ι (PrimeSpectrum.comap ρ z) (d i) (f i) (g i))
    (a : Fin m) (e : ℕ) (he : 1 ≤ e)
    (hdegree : (∀ j, j < a → d j ≤ e) ∧ (∀ i, a ≤ i → e ≤ d i))
    (q w : Fin m → LocalChart ρ z)
    (hearlier : ∀ j, j < a → InOrderSpace r p (d j) (φ j) ∧
      q j = g j - w j ∧
      w j ∈ exceptionalIdeal x y (PrimeSpectrum.comap ρ z) * prefixIdeal g j ∧
      adicOrder (IsLocalRing.maximalIdeal (LocalChart ρ z)) (q j) = d j)
    (hjet : transformIdeal ρ z ≤
      prefixIdeal q a ⊔ IsLocalRing.maximalIdeal (LocalChart ρ z) ^ e) :
    prefixIdeal q a ⊓
        (exceptionalIdeal x y (PrimeSpectrum.comap ρ z) ⊔
          IsLocalRing.maximalIdeal (LocalChart ρ z) ^ e) ≤
      exceptionalIdeal x y (PrimeSpectrum.comap ρ z) * prefixIdeal q a ⊔
        IsLocalRing.maximalIdeal (LocalChart ρ z) ^ e := by
  sorry

end Hironaka
