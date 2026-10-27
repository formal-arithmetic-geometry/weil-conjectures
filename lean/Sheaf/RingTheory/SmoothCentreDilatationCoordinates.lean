module

public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Kaehler.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Adjoin.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
import WeilConjectures.RingTheory.EtalePolynomialStandardSmooth

/-!
# Smooth coordinate charts for dilatations

Source: Bosch--Lütkebohmert--Raynaud, Néron Models, §3.2 Proposition 3 and
§3.3 Proposition 5, printed pp.64 and 70.
(blueprint: lem-sfb-smooth-centre-dilatation-coordinates)
-/

@[expose] public section

set_option autoImplicit false

universe u

open scoped TensorProduct

namespace Algebra

/-- Dividing the normal coordinates of an étale chart by a uniformizer gives an étale
chart with the stated presentation, generic fibre and differential basis.
Source: BLR, Néron Models, §3.2 Proposition 3 and §3.3 Proposition 5, pp.64,70.
(blueprint: lem-sfb-smooth-centre-dilatation-coordinates)

Here `J` and `C'` are specified by equalities to the actual ideal and fraction subalgebra;
they are names for those constructions, not additional geometric assumptions. The elements
`z'` and the isomorphism are characterized on generators, so no arbitrary map is substituted
for a canonical one. The `IsLocalization.Away` clause uses the inclusion of the subalgebra
into the original localization and expresses equality of the two generic fibres.

Proof. Put P = R[y,z] and Q = R[y,t], with z mapping to πt. Evaluation and the tensor
universal property identify Q ⊗[P] C with B = C[t]/(πt-z), in both directions on generators
(def-weil-pbc-mv-polynomial-ring, def-weil-pbc-module-tensor-product). Étale base change
(lem-weil-pbc-etale-ring-base-change, lem-weil-pbc-etale-ring-map-iff-etale-affine) makes
Q → B étale. The polynomial étale standard-smooth lemma, standard-smooth implies smooth,
and smooth implies flat give R-flatness (lem-weil-pbc-etale-polynomial-standard-smooth,
lem-weil-pbc-standard-smooth-is-smooth, lem-weil-pbc-smooth-ring-map-flat). Since R is a
DVR and π is nonzero, flatness makes B π-torsion-free
(lem-trf-flat-module-torsionfree-domain). Inverting π identifies B[1/π] with C[1/π] by
sending t to z/π, so B embeds there with image C[z/π]. Writing each element of J as
πc₀ + ∑ zⱼcⱼ identifies this image with the specified adjoin of all b/π. This proves the
presentation and the localization claim. The affine smoothness bridge and smooth-flat
lemma give the scheme clauses (lem-weil-pbc-smooth-ring-map-iff-smooth-affine,
lem-pc-smooth-flat). A DVR is Noetherian and smoothness includes finite presentation,
so the finite-type Noetherian lemma gives Noetherianity
(lem-weil-pbc-finite-type-algebra-noetherian). The formally étale differential base-change
lemma and polynomial differential basis give the basis dy,dz'
(lem-trf-formally-etale-differentials-base-change,
lem-weil-pbc-polynomial-ring-kahler-basis). Finally the universal differential map sends
dy to dy, and z = πz' together with dπ = 0 gives dz = π dz' by Leibniz
(def-weil-pbc-kahler-differentials). This also covers empty coordinate sets. -/
theorem smooth_centre_dilatation_coordinates
    (R C : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [CommRing C] [Algebra R C] (π : R) (hπ : Irreducible π)
    (r n : ℕ) (y : Fin r → C) (z : Fin n → C)
    (hEtale : AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map
      (CommRingCat.ofHom (MvPolynomial.aeval (R := R) (Sum.elim y z)).toRingHom)))
    (J : Ideal C)
    (hJ : J = Ideal.span ({algebraMap R C π} ∪ Set.range z))
    (C' : Subalgebra C (Localization.Away (algebraMap R C π)))
    (hC' : C' = Algebra.adjoin C
      {x | ∃ b ∈ J, x = algebraMap C (Localization.Away (algebraMap R C π)) b *
        IsLocalization.Away.invSelf (algebraMap R C π)}) :
    ∃ (z' : Fin n → C')
      (e : (MvPolynomial (Fin n) C ⧸ Ideal.span
        (Set.range (fun j : Fin n =>
          MvPolynomial.C (algebraMap R C π) * MvPolynomial.X j -
            MvPolynomial.C (z j)))) ≃ₐ[C] C'),
      (∀ j : Fin n, e (Ideal.Quotient.mk _ (MvPolynomial.X j)) = z' j) ∧
      (∀ j : Fin n, (z' j : Localization.Away (algebraMap R C π)) =
        algebraMap C (Localization.Away (algebraMap R C π)) (z j) *
          IsLocalization.Away.invSelf (algebraMap R C π)) ∧
      AlgebraicGeometry.Etale (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (MvPolynomial.aeval (R := R)
          (Sum.elim (fun i : Fin r => algebraMap C C' (y i)) z')).toRingHom)) ∧
      AlgebraicGeometry.Smooth (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap R C'))) ∧
      AlgebraicGeometry.Flat (AlgebraicGeometry.Spec.map
        (CommRingCat.ofHom (algebraMap R C'))) ∧
      IsNoetherianRing C' ∧
      IsLocalization.Away (algebraMap R C' π)
        (Localization.Away (algebraMap R C π)) ∧
      ∃ b : Module.Basis (Fin r ⊕ Fin n) C' (KaehlerDifferential R C'),
        (∀ i : Fin r, b (Sum.inl i) =
          KaehlerDifferential.D R C' (algebraMap C C' (y i))) ∧
        (∀ j : Fin n, b (Sum.inr j) = KaehlerDifferential.D R C' (z' j)) ∧
        (∀ i : Fin r, KaehlerDifferential.mapBaseChange R C C'
          (1 ⊗ₜ[C] KaehlerDifferential.D R C (y i)) = b (Sum.inl i)) ∧
        (∀ j : Fin n, KaehlerDifferential.mapBaseChange R C C'
          (1 ⊗ₜ[C] KaehlerDifferential.D R C (z j)) =
            algebraMap R C' π • b (Sum.inr j)) := by
  sorry

end Algebra
