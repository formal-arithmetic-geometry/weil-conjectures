module

public import WeilConjectures.RingTheory.QuasiFiniteAtPrime
public import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Sheaf.Paper.QuasiFiniteOverPolynomialAlgebra
import WeilConjectures.RingTheory.QuasiFiniteFourRings
import Mathlib.RingTheory.TensorProduct.MvPolynomial

/-! # Localized polynomial charts and their field fibres

Source: Stacks Project, algebra.tex, Tag 00QK
(lemma-finite-type-domain-over-valuation-ring-dim-fibres), polynomial-chart passage,
expanded by Tags 00QE, 00PN, 00DK, 00DL, 00E3 and 00CP
(blueprint: lem-trf-localized-polynomial-chart-fibres).

Tensor factors are written in the order `c ⊗[A] D`, using the canonical symmetry
with the order `D ⊗[A] c` in the source.
-/

@[expose] public section

set_option autoImplicit false

universe u v w

open scoped TensorProduct

namespace Algebra

/-- The induced polynomial chart on a field fibre, sending each variable to
`1 ⊗ α(X i)` and each coefficient to its structural image.
Source: Stacks Project, algebra.tex, Tags 00QK and 00PN, field-fibre polynomial maps
(blueprint: lem-trf-localized-polynomial-chart-fibres). -/
noncomputable def localizedPolynomialChartFieldMap
    (A : Type u) (D : Type v) (c : Type w)
    [CommRing A] [CommRing D] [CommRing c] [Algebra A D] [Algebra A c]
    (n : ℕ) (g : D) (α : MvPolynomial (Fin n) A →ₐ[A] Localization.Away g) :
    MvPolynomial (Fin n) c →ₐ[c] c ⊗[A] Localization.Away g :=
  MvPolynomial.aeval fun i ↦ (1 : c) ⊗ₜ[A] α (MvPolynomial.X i)

/-- A finite type algebra over a local ring admits a principal quasi-finite polynomial
chart with the prescribed local special-fibre dimension. It remains quasi-finite
on every field fibre, localization commutes canonically with those fibres, and
local special-fibre dimension and generic-fibre fraction fields are preserved.
Source: Stacks Project, algebra.tex, Tag 00QK, polynomial-chart passage, with
Tags 00QE, 00PN, 00DK, 00DL, 00E3 and 00CP
(blueprint: lem-trf-localized-polynomial-chart-fibres).

Proof:
1. Contract `Q` to `q` in `D`. Its contraction to `A` is the maximal ideal,
since the residue field maps injectively to the domain obtained by quotienting by
`Q`. Identify the fibre prime using lem-weil-pbc-fibre-ring-primes-bijection.
Apply lem-weil-pbc-quasi-finite-over-polynomial-algebra to obtain `g` and `α`.
2. Adjoin the images of finitely many algebra generators of `D` and `1/g` to
generate the localization. Their tensors generate each field fibre. This uses
the tensor pushout universal property and proves both finite type assertions.
3. Polynomial scalar extension identifies the base-changed source with `c[t]`.
The square commutes on coefficients and variables; pure tensors are products
of images from the two sides. Apply lem-weil-pbc-quasi-finite-four-rings at
every prime to obtain finite type and quasi-finiteness of the displayed map.
4. Apply lem-weil-pbc-algebra-localization-away-base-change. Its fraction formula
is the displayed formula, and characterizes the canonical algebra isomorphism.
5. At the residue field, `g` avoids `Q`. The localization spectrum embedding
identifies the fibre spectrum with the basic open containing `Q`, and gives
`Qg`. Apply lem-weil-pbc-dimension-at-point-open-subspace and transport dimension
through this homeomorphism to get local dimension `n`.
6. Under the domain and injectivity assumptions, `g ≠ 0` since it avoids a prime.
The fraction relation proves injectivity into the localization and its domain
property. Apply lem-weil-pbc-generic-fibre-localization-domain-irreducible to
`D` and its localization: the generic fibres are nonzero domains, and `g`
stays nonzero. Step 4 identifies their principal localization.
7. The localization universal property extends the inclusion of the generic
fibre into its fraction field. Extending injective maps into fields by
`a/b ↦ f(a)/f(b)` gives mutually inverse fraction-field maps. Their formulas
show they fix the fraction field of `A`. -/
theorem exists_localizedPolynomialChart_fibres
    (A : Type u) (D : Type v) [CommRing A] [IsLocalRing A]
    [CommRing D] [Algebra A D] [Algebra.FiniteType A D]
    (Q : PrimeSpectrum (IsLocalRing.ResidueField A ⊗[A] D)) (n : ℕ)
    (hdim : topologicalKrullDimAt Q = (n : WithBot ℕ∞)) :
    ∃ (g : D)
      (_ : g ∉ (Q.comap (TensorProduct.includeRight
        (R := A) (A := IsLocalRing.ResidueField A) (B := D)).toRingHom).asIdeal)
      (α : MvPolynomial (Fin n) A →ₐ[A] Localization.Away g)
      (hft : α.toRingHom.FiniteType),
      Algebra.FiniteType A (Localization.Away g) ∧
      (∀ p : PrimeSpectrum (Localization.Away g),
        @IsQuasiFiniteAtPrime (MvPolynomial (Fin n) A) (Localization.Away g)
          _ _ α.toRingHom.toAlgebra hft p) ∧
      (∀ (c : Type w) [Field c] [Algebra A c],
        ∃ hftc : (localizedPolynomialChartFieldMap A D c n g α).toRingHom.FiniteType,
          (∀ p : PrimeSpectrum (c ⊗[A] Localization.Away g),
            @IsQuasiFiniteAtPrime (MvPolynomial (Fin n) c) (c ⊗[A] Localization.Away g)
              _ _ (localizedPolynomialChartFieldMap A D c n g α).toRingHom.toAlgebra
              hftc p) ∧
          Algebra.FiniteType c (c ⊗[A] Localization.Away g) ∧
          ∃ e : c ⊗[A] Localization.Away g ≃ₐ[c]
              Localization.Away ((1 : c) ⊗ₜ[A] g),
            ∀ (d : D) (j : ℕ) (a : c),
              e (a ⊗ₜ[A] IsLocalization.mk' (M := Submonoid.powers g) (Localization.Away g) d
                ⟨g ^ j, j, rfl⟩) =
              IsLocalization.mk' (M := Submonoid.powers ((1 : c) ⊗ₜ[A] g))
                (Localization.Away ((1 : c) ⊗ₜ[A] g))
                (a ⊗ₜ[A] d) ⟨((1 : c) ⊗ₜ[A] g) ^ j, j, rfl⟩) ∧
      (∃ e : PrimeSpectrum (IsLocalRing.ResidueField A ⊗[A] Localization.Away g) ≃ₜ
          (PrimeSpectrum.basicOpen ((1 : IsLocalRing.ResidueField A) ⊗ₜ[A] g)),
        (∀ p, (e p).val = p.comap
          (TensorProduct.map (AlgHom.id A (IsLocalRing.ResidueField A))
            (IsScalarTower.toAlgHom A D (Localization.Away g))).toRingHom) ∧
        ∃ Qg : PrimeSpectrum (IsLocalRing.ResidueField A ⊗[A] Localization.Away g),
          (e Qg).val = Q ∧ topologicalKrullDimAt Qg = (n : WithBot ℕ∞)) ∧
      (∀ [IsDomain A] [IsDomain D], Function.Injective (algebraMap A D) →
        g ≠ 0 ∧ IsDomain (Localization.Away g) ∧
        Function.Injective (algebraMap A (Localization.Away g)) ∧
        IsDomain (FractionRing A ⊗[A] D) ∧
        IsDomain (FractionRing A ⊗[A] Localization.Away g) ∧
        Nonempty ((FractionRing A ⊗[A] Localization.Away g) ≃ₐ[FractionRing A]
          Localization.Away ((1 : FractionRing A) ⊗ₜ[A] g)) ∧
        Nonempty (FractionRing (FractionRing A ⊗[A] Localization.Away g) ≃ₐ[FractionRing A]
          FractionRing (FractionRing A ⊗[A] D))) := by
  sorry

end Algebra
