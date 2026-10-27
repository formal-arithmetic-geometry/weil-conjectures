module

public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# An fppf cover avoiding unimodular affine linear forms

Source: Stacks Project, Tags 00HQ, 00HT, 00HC, 00E3 and 00FB; the explicit
principal-polynomial-open specialization of Conrad, Reductive group schemes,
Proposition 4.3.1, printed p.130, before (4.3.2).
(blueprint: lem-sfb-unimodular-linear-forms-fppf-cover)

The polynomial, localization and morphism below name the canonical constructions
in the statement. Flatness, surjectivity and local finite presentation say precisely
that the singleton morphism is an fppf covering.
-/

@[expose] public section

universe u

set_option autoImplicit false

open CategoryTheory

namespace AlgebraicGeometry

/-- The product of the affine linear forms, including the empty product `1`.
Source: Conrad, Proposition 4.3.1, p.130, common-translate argument before (4.3.2).
(blueprint: lem-sfb-unimodular-linear-forms-fppf-cover) -/
noncomputable def unimodularLinearFormsPolynomial
    {R : Type u} [CommRing R] {n : ℕ} (b d : Fin n → R) : Polynomial R :=
  ∏ i : Fin n, (Polynomial.C (b i) * Polynomial.X + Polynomial.C (d i))

/-- The concrete ring `R[Z][1 / ∏ i, (bᵢ Z + dᵢ)]`.
Source: Stacks Project, Algebra, localization (Tag 00CM); Conrad, Proposition 4.3.1.
(blueprint: lem-sfb-unimodular-linear-forms-fppf-cover) -/
noncomputable abbrev unimodularLinearFormsAlgebra
    {R : Type u} [CommRing R] {n : ℕ} (b d : Fin n → R) : Type u :=
  Localization.Away (unimodularLinearFormsPolynomial b d)

/-- The canonical spectrum morphism for the polynomial localization, induced by
`R → R[Z] → R[Z][1/P]`.
Source: Stacks Project, Algebra, Tags 00E2 and 00E3; Conrad, Proposition 4.3.1.
(blueprint: lem-sfb-unimodular-linear-forms-fppf-cover) -/
noncomputable def unimodularLinearFormsCover
    {R : Type u} [CommRing R] {n : ℕ} (b d : Fin n → R) :
    Spec (CommRingCat.of (unimodularLinearFormsAlgebra b d)) ⟶ Spec (CommRingCat.of R) :=
  Spec.map (CommRingCat.ofHom
    ((algebraMap (Polynomial R) (unimodularLinearFormsAlgebra b d)).comp Polynomial.C))

/-- Simultaneously avoid finitely many unimodular affine linear forms by the canonical
polynomial-localization fppf cover. The final clause is the image of `bᵢ Z + dᵢ`,
hence is `bᵢ z + dᵢ` for the image `z` of `Z` in the localization.

Source: Stacks Project, Tags 00HQ, 00HT, 00HC, 00E3 and 00FB; Conrad,
Proposition 4.3.1, printed p.130, before (4.3.2).
(blueprint: lem-sfb-unimodular-linear-forms-fppf-cover)

Proof plan:
1. The powers of `Z` give a free `R`-basis of `R[Z]`, so it is flat over `R`
   (lem-weil-pbc-projective-module-flat).
2. Localization is flat (lem-weil-pbc-localization-flat), and compositions of flat
   ring maps are flat (lem-weil-pbc-flat-ring-map-comp). Translate to spectra using
   lem-weil-pbc-flat-ring-map-iff-flat-affine.
3. The localization has the finite presentation `R[Z,T]/(T P(Z) - 1)`: send `T`
   to the inverse of `P`, and send a fraction `a/P^m` to `a T^m`. The localization
   fraction-equality relation makes this inverse well-defined. This proves local
   finite presentation by def-sbc-locally-finite-presentation.
4. For a prime `p` of `R`, the coefficientwise kernel of `R[Z] → (R/p)[Z]` is prime,
   since the target is a domain (lem-weil-pbc-polynomial-ring-domain). Its contraction
   is `p`. Unimodularity prevents both coefficients of any factor from lying in `p`,
   so no factor, and hence no product `P`, lies in this prime.
5. The prime avoids all powers of `P` and therefore lifts to the localization by
   lem-weil-pbc-localization-spectrum-embedding. This proves surjectivity on points.
6. The inverse of the image of the ith factor is `P⁻¹` times the product of all other
   factors. The three morphism properties give the singleton fppf covering. For `n=0`
   the product is `1`; for the zero ring there are no primes and its sole element is
   a unit. Both cases are included without additional hypotheses. -/
theorem unimodular_linear_forms_fppf_cover
    {R : Type u} [CommRing R] {n : ℕ} (b d : Fin n → R)
    (hunimodular : ∀ i, ∃ r s : R, r * b i + s * d i = 1) :
    Flat (unimodularLinearFormsCover b d) ∧
      Surjective (unimodularLinearFormsCover b d) ∧
      LocallyOfFinitePresentation (unimodularLinearFormsCover b d) ∧
      ∀ i : Fin n, IsUnit
        (algebraMap (Polynomial R) (unimodularLinearFormsAlgebra b d)
          (Polynomial.C (b i) * Polynomial.X + Polynomial.C (d i))) := by
  sorry

end AlgebraicGeometry
