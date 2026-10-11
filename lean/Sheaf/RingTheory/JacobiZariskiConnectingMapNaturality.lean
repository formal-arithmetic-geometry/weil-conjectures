/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group C1
-/
module

public import Sheaf.RingTheory.JacobiZariskiHomologySequence
public import Mathlib.RingTheory.Extension.ExtendScalars

/-!
# Naturality of the Jacobi–Zariski connecting map for a quotient

Source: Stacks Project, Algebra, Tag 00S2, and More on Algebra, Tags 07E4 and 07E5
(blueprint: lem-weil-pbc-jacobi-zariski-connecting-map-naturality).
-/

@[expose] public section

universe u v w

open TensorProduct KaehlerDifferential

namespace Algebra

/-- Source: Stacks Project, Tag 00S2 (whose proof omits the definitions of the maps),
and the diagram in Tag 07E5, equivalence of (3) and (4)
(blueprint: lem-weil-pbc-jacobi-zariski-connecting-map-naturality).

The quotient extension `P` has ring `B` and kernel `I`; its cotangent module is `I/I²`.
The map `P.cotangentComplex` is the conormal differential, and
`P.h1CotangentEquivCotangent` is the canonical quotient isomorphism. The connecting
maps are those of `jacobiZariski_homology_sequence`, with its coefficient formula.
Existence of the linear comparison `c`, with the displayed generator formula, expresses
that this formula is well defined. All four maps are bundled linear maps over the quotient.

Proof (the node's five steps).
1. Use the polynomial differential basis
(`lem-weil-pbc-polynomial-ring-kahler-basis-any-variables`) to identify the kernel with
cycles in the canonical polynomial presentation. The coefficient map S[C] to B[C]
fixes each variable and commutes with evaluation; presentation functoriality
(`lem-weil-pbc-nl-presentation-h1-functoriality`) gives the map on these cycles.
2. Differentiating coefficients is an R-derivation. It kills products of two kernel
elements, and multiplication by a polynomial acts through its evaluation, so it descends
to a C-linear map on the conormal module. The universal property of Kahler differentials
(`def-weil-pbc-kahler-differentials`) and tensor balancing give c. The Leibniz rule
likewise gives the conormal differential f mod I² to 1 tensor df.
3. Choose a set-theoretic section of B to C. Evaluate the variables at these lifts.
The quotient isomorphism (`lem-weil-pbc-jacobi-zariski-surjection-h1`) sends the mapped
cycle to this evaluation modulo I², independently of the section.
4. Differentiate this evaluation using Leibniz. The coefficient terms give c applied
to the coefficient derivative. The other terms are the evaluated partial derivatives
of the cycle times the differentials of the lifts, and vanish because it is a cycle.
5. This proves the composite identity on every cycle. With S = B, presentation
functoriality makes the H1 map the identity and tensor generators make c the identity,
giving the last equality. The polynomial evaluations use
`def-weil-pbc-mv-polynomial-ring`; H1 uses `def-weil-pbc-smooth-ring-map`. -/
theorem jacobiZariski_connectingMap_naturality
    (R : Type u) (S : Type v) (B : Type w)
    [CommRing R] [CommRing S] [CommRing B]
    [Algebra R S] [Algebra S B] [Algebra R B] [IsScalarTower R S B]
    (I : Ideal B) :
    let C := B ⧸ I
    let P := Extension.ofSurjective (IsScalarTower.toAlgHom R B C)
      (Ideal.Quotient.mk_surjective : Function.Surjective (Ideal.Quotient.mk I))
    let ι := H1Cotangent.map S B C C
    let θ := P.h1CotangentEquivCotangent
    let partialS := H1Cotangent.δ R S C
    let partialB := H1Cotangent.δ R B C
    let δ := P.cotangentComplex
    ∃ c : C ⊗[S] Ω[S⁄R] →ₗ[C] C ⊗[B] Ω[B⁄R],
      (∀ (x : C) (s : S),
        c (x ⊗ₜ[S] D R S s) = x ⊗ₜ[B] D R B (algebraMap S B s)) ∧
      (δ.comp (θ.toLinearMap.comp ι) = c.comp partialS) ∧
      (δ.comp θ.toLinearMap = partialB) := by
  sorry

end Algebra
