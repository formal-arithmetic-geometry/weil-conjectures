module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.RingTheory.FiniteType
public import Mathlib.RingTheory.Noetherian.Defs
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.Algebra.Module.LocalizedModule.Exact
import WeilConjectures.AlgebraicGeometry.PrincipalLocalizationNaiveCotangent
import WeilConjectures.RingTheory.EtaleRingMapConormalCriterion
import WeilConjectures.RingTheory.ExistsAnnihilatorOfSubsingletonLocalizedModule

/-! # Ideal-power torsion of ordinary conormal cohomology

Source: Stacks Project, restricted.tex, Tags 0ALQ and 0AKA; algebra.tex, Section 00S0
(blueprint: lem-per-etale-supported-cotangent-completion).
-/

@[expose] public section

universe u

open AlgebraicGeometry

namespace Algebra

/-- The canonical polynomial conormal differential in the coordinate basis `dy_j`.
Its source is the kernel modulo its square with the quotient `C`-module structure.
The differential sends `[f]` to `(α (MvPolynomial.pderiv j f))_j`: Mathlib's
`Extension.cotangentComplex_mk` sends `[f]` to `1 ⊗ df`, and
`KaehlerDifferential.mvPolynomialBasis_repr_apply` gives precisely these coordinates.

Source: Stacks Project, algebra.tex, Section 00S0 and Tag 00RX
(blueprint: lem-per-etale-supported-cotangent-completion). -/
noncomputable def polynomialConormalDifferential
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    {s : ℕ} (α : MvPolynomial (Fin s) A →ₐ[A] C) (hα : Function.Surjective α) :
    (Extension.ofSurjective α hα).Cotangent →ₗ[C] (Fin s → C) :=
  letI : Algebra (MvPolynomial (Fin s) A) C := α.toAlgebra
  ((KaehlerDifferential.mvPolynomialBasis A (Fin s)).baseChange C).equivFun.toLinearMap.comp
    (Extension.ofSurjective α hα).cotangentComplex

/-- Both ordinary conormal cohomology modules of any finite polynomial presentation
are finite and annihilated by one power of the ideal over whose complement the algebra
is etale. Scalars from `A` act through `algebraMap A C`.

Source: Stacks Project, restricted.tex, Tag 0ALQ (first and converse paragraphs of the
proof), Tag 0AKA (last paragraph); algebra.tex, Tag 00IM
(blueprint: lem-per-etale-supported-cotangent-completion).

Proof:
1. Leibniz makes differentiation followed by α kill K² and be C-linear; the displayed
   canonical differential is this descended map (def-weil-pbc-polynomial-partial-derivative).
2. The finite-type algebras A[y] and C are Noetherian
   (lem-weil-pbc-finite-type-algebra-noetherian). Ideal generators of K generate K/K²;
   the Noetherian submodule theorem gives finiteness of the kernel
   (lem-weil-pbc-noetherian-submodule-finite). The cokernel is a quotient of C^s.
3. Choose generators a_j of H. The principal open D(g_j), for g_j the image of a_j,
   lies over the complement of V(H). Identify it with Spec(C[g_j⁻¹]) using
   lem-weil-pbc-affine-open-section-vanishing-prime and
   lem-weil-pbc-principal-localization-open-immersion. Etale open restriction and
   composition (lem-a1-etale-open-restriction,
   lem-weil-pbc-etale-composition-cancellation) make C[g_j⁻¹] etale over A.
4. Add an inverse variable with relation a_j z - 1. The principal-localization
   presentation and its splitting (lem-weil-pbc-principal-localization-naive-cotangent)
   identify the new conormal complex with the localized old one plus multiplication
   by the unit g_j. The etale conormal criterion
   (lem-weil-pbc-etale-ring-map-conormal-criterion), in the polynomial differential
   basis (lem-weil-pbc-polynomial-ring-kahler-basis), makes both differentials bijective.
5. Exact localization (lem-weil-pbc-localization-module-exact) now gives zero
   localizations of the kernel and cokernel at every g_j.
6. Finiteness and lem-weil-pbc-finite-module-localization-zero-annihilator give powers
   g_j^n killing each module. Choose e_j at least 1 and at least both such exponents.
7. If H = 0, take b = 1. Otherwise take b = 1 + sum_j (e_j - 1). Each degree-b
   monomial in the generators of H contains some a_j^e_j, so kills both modules.
   These monomials generate H^b, giving the claimed simultaneous annihilation. -/
theorem finite_and_ideal_pow_annihilates_polynomialConormal
    {A C : Type u} [CommRing A] [CommRing C] [Algebra A C]
    [IsNoetherianRing A] (H : Ideal A)
    (hC : (algebraMap A C).FiniteType)
    (het : AlgebraicGeometry.Etale ((Spec.map (CommRingCat.ofHom (algebraMap A C))) ∣_
      (⟨(PrimeSpectrum.zeroLocus (H : Set A))ᶜ,
        (PrimeSpectrum.isClosed_zeroLocus (H : Set A)).isOpen_compl⟩ : (Spec (.of A)).Opens)))
    (s : ℕ) (α : MvPolynomial (Fin s) A →ₐ[A] C) (hα : Function.Surjective α) :
    Module.Finite C (LinearMap.ker (polynomialConormalDifferential α hα)) ∧
    Module.Finite C ((Fin s → C) ⧸ LinearMap.range (polynomialConormalDifferential α hα)) ∧
    ∃ b : ℕ, (∀ a ∈ H ^ b,
      ∀ m : LinearMap.ker (polynomialConormalDifferential α hα),
        algebraMap A C a • m = 0) ∧
      (∀ a ∈ H ^ b,
        ∀ m : (Fin s → C) ⧸ LinearMap.range (polynomialConormalDifferential α hα),
          algebraMap A C a • m = 0) := by
  sorry

end Algebra
