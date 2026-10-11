/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-! # Etale ring maps and the conormal criterion

Source: literature/stacks-project/algebra.tex, Definition Tag 00U1 and Lemma Tag 00U9
(blueprint: lem-weil-pbc-etale-ring-map-conormal-criterion)
-/

@[expose] public section

universe u

namespace Algebra

/-- The derivative formula descends to an S-linear map on J/J², and etaleness is
 equivalent to its bijectivity. The S-action is transported along P/J ≃ S.

Source: literature/stacks-project/algebra.tex, Definition Tag 00U1, text before Tag 00S1,
Lemma Tag 00U9; morphisms.tex, Tag 02GJ
(blueprint: lem-weil-pbc-etale-ring-map-conormal-criterion).

Proof: the Leibniz rule makes the derivative vanish on J² and gives S-linearity.
The polynomial Kahler basis (lem-weil-pbc-polynomial-ring-kahler-basis) identifies
S tensor Ω[P/R] with the free module on the dx_i; polynomial H₁ vanishes by
lem-weil-pbc-polynomial-ring-h1-cotangent-vanishing. The Jacobi-Zariski sequence
(lem-weil-pbc-jacobi-zariski-quotient-smooth) identifies the kernel with H₁(L[S/R])
and the cokernel with Ω[S/R]. The finitely generated kernel gives finite presentation.
Definition 00U1 then gives etaleness iff both kernel and cokernel vanish; the affine
comparison lem-weil-pbc-etale-ring-map-iff-etale-affine (Mathlib's
`HasRingHomProperty @Etale RingHom.Etale`) gives the scheme formulation. -/
theorem etale_ring_map_conormal_criterion
    {R : Type u} {S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (n : ℕ) (α : MvPolynomial (Fin n) R →ₐ[R] S)
    (hα : Function.Surjective α)
    (hfg : (RingHom.ker α.toRingHom).FG) :
    let J := RingHom.ker α.toRingHom
    let e := RingHom.quotientKerEquivOfSurjective hα
    letI : Module S J.Cotangent := Module.compHom J.Cotangent e.symm.toRingHom
    ∃ d : J.Cotangent →ₗ[S] (Fin n → S),
      (∀ (g : J) (i : Fin n),
        d (Ideal.toCotangent J g) i = α (MvPolynomial.pderiv i g.1)) ∧
      (AlgebraicGeometry.Etale
          (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap R S))) ↔
        Function.Bijective d) := by
  sorry

end Algebra
