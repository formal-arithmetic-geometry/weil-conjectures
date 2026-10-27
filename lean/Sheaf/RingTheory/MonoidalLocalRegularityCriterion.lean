module

public import Sheaf.AlgebraicGeometry.FineSaturatedLogBlowup
public import Mathlib.Algebra.AffineMonoid.Irreducible
public import Mathlib.GroupTheory.MonoidLocalization.Finite
public import WeilConjectures.RingTheory.IsRegularSystemOfParameters
import Mathlib.RingTheory.LocalRing.Module
import WeilConjectures.RingTheory.RegularLocalQuotientKernelParameters
import WeilConjectures.RingTheory.RegularLocalGeneratorsRegularSequence

/-!
# The monoidal local regularity criterion

Source: Illusie--Laszlo--Orgogozo, Exposé VI 1.2, 1.6--1.7, pp. 69--70,
and Exposé VIII 3.4.3, p. 110; the local algebra extracted in the DAG
(blueprint: lem-trf-monoidal-local-regularity-criterion).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open scoped TensorProduct

namespace RingTheory

/-- A sharp fs monoid chart contracting every monoid ideal detects ordinary regularity
and extends arbitrary lifted quotient parameters to ordinary parameters.

The named ideal `I` is exactly the ideal of nonzero monomials, and `r` is the rational
rank of the group completion. The basis is stated in the actual quotient `I / m I`.
An enumeration `p` is injective with range all indecomposables. A chosen additive
isomorphism `e` supplies the standard monoid coordinates in the final clause.

Source: ILO VI 1.2, 1.6--1.7, pp. 69--70, VIII 3.4.3, p. 110
(blueprint: lem-trf-monoidal-local-regularity-criterion).

Proof plan:
1. Take an inclusion-minimal finite generating set `S`, omitting zero. Every
indecomposable lies in `S`, since a sum of two or more nonzero generators decomposes it.
If `s` in `S` equals `x + y` with both terms nonzero, express `x` and `y` in `S`.
An occurrence of `s` would, by cancellation, give a sum equal to zero; sharpness
would force `x` or `y` to vanish. Thus neither expression uses `s`, contradicting
minimality. Hence `S` is exactly the indecomposables. If a positive multiple of a
group-completion element `g` is zero, saturation puts both `g` and `-g` in the
monoid. Sharpness then gives `g = 0`, proving torsion freeness.
2. The indecomposable images generate `I`. For each omitted generator, contract the
union of the principal monoid ideals of the other generators. Its image cannot lie
in the ideal of the other images. A nontrivial residue-field relation would let one
omit that generator modulo `m I`; Nakayama (lem-weil-pbc-nakayama-local-generators)
would then let one omit it in `I`, a contradiction. Hence the displayed classes are a basis.
3. The indecomposables span the rationalized group completion, so `r ≤ n`. Equality
makes them a rational basis, and torsion freeness makes the surjection from `N^n`
injective. Conversely an isomorphism with `N^r` preserves its `r` indecomposables.
4. If `A` is regular, apply lem-weil-pbc-regular-local-quotient-kernel-parameters to
express `I` as a parameter prefix of length `c`. Apply
lem-weil-pbc-regular-local-generators-regular-sequence to this same prefix to get
`dim(A/I) = dim(A) - c`. The dimension formula gives `c = r`; the basis in step 2
gives `n ≤ c`, hence `n = r`.
5. If `n = r`, any lifts in `m` of parameters downstairs, together with the monoid
basis images, generate `m`: lift coefficients modulo `I` and then generate the
remaining element of `I` by monomials. Their number is `dim A`, proving regularity
and the regular-system-of-parameters assertion. Empty monoid and parameter lists
are allowed; rank zero forces the torsion-free group completion and monoid to vanish. -/
theorem monoidal_local_regularity_criterion
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (P : Type v) [AddCommMonoid P]
    (hfs : AlgebraicGeometry.IsFineSaturatedMonoid (Multiplicative P))
    (hsharp : ∀ p : P, IsAddUnit p → p = 0)
    (a : Multiplicative P →* A)
    (ha : ∀ p : P, p ≠ 0 → a (Multiplicative.ofAdd p) ∈ IsLocalRing.maximalIdeal A)
    (hcontract : ∀ J : Set P, (∀ p ∈ J, ∀ q : P, p + q ∈ J) →
      ∀ p : P, a (Multiplicative.ofAdd p) ∈
        Ideal.span ((fun q : P ↦ a (Multiplicative.ofAdd q)) '' J) ↔ p ∈ J)
    (I : Ideal A)
    (hI : I = Ideal.span ((fun p : P ↦ a (Multiplicative.ofAdd p)) '' {p | p ≠ 0}))
    (r : ℕ) (hr : r = Module.finrank ℚ (ℚ ⊗[ℤ] Algebra.GrothendieckAddGroup P))
    [IsRegularLocalRing (A ⧸ I)]
    (hdim : ringKrullDim A = ringKrullDim (A ⧸ I) + (r : WithBot ℕ∞)) :
    {p : P | AddIrreducible p}.Finite ∧
      AddSubmonoid.closure {p : P | AddIrreducible p} = ⊤ ∧
      IsAddTorsionFree (Algebra.GrothendieckAddGroup P) ∧
      (∀ (n : ℕ) (p : Fin n → P), Function.Injective p →
        Set.range p = {q : P | AddIrreducible q} →
        (∃ b : Module.Basis (Fin n) (A ⧸ IsLocalRing.maximalIdeal A)
          (I ⧸ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A I))),
          ∀ i : Fin n, ∃ x : I, (x : A) = a (Multiplicative.ofAdd (p i)) ∧
            b i = Submodule.mkQ (IsLocalRing.maximalIdeal A • (⊤ : Submodule A I)) x) ∧
        (IsRegularLocalRing A ↔ n = r) ∧
        (n = r ↔ Nonempty (P ≃+ (Fin r → ℕ)))) ∧
      (∀ (e : P ≃+ (Fin r → ℕ)) (bs : List A),
        (∀ b ∈ bs, b ∈ IsLocalRing.maximalIdeal A) →
        IsLocalRing.IsRegularSystemOfParameters (bs.map (Ideal.Quotient.mk I)) →
        IsLocalRing.IsRegularSystemOfParameters
          (List.ofFn (fun i : Fin r ↦
            a (Multiplicative.ofAdd (e.symm (Pi.single i 1)))) ++ bs)) := by
  sorry

end RingTheory
