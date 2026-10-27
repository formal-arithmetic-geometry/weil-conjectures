/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q27
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import WeilConjectures.AlgebraicGeometry.Morphisms.FiberDegree
public import Mathlib.RingTheory.TensorProduct.Quotient
import Sheaf.AlgebraicGeometry.AffineFormallySmooth
import Mathlib.RingTheory.Smooth.Basic
import Mathlib.RingTheory.FinitePresentation
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import WeilConjectures.RingTheory.Smooth.AugmentationFirstOrderCoordinates
import WeilConjectures.RingTheory.Smooth.AugmentationPolynomialTruncations
import Mathlib.RingTheory.LocalProperties.Projective
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.RingHom.Flat

/-!
# Finite infinitesimal neighborhoods of a smooth affine section

Source: Conrad, Reductive group schemes, proof of Proposition 2.1.6, pp. 62–63;
Stacks Project, Tags 05D5, 00TN, 0564 and 00NX.
(blueprint: lem-sfb-smooth-section-finite-jets)

The section is encoded by its algebra retraction. The algebra equivalence uses the
right scalar action on the tensor products, passed explicitly rather than installed
as a local instance. The scheme isomorphism respects both ambient and base projections.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace AlgebraicGeometry

/-- The base change of the retraction of a smooth affine section: on pure tensors
it sends `b ⊗ a'` to `ε(b) a'`.

Source: Conrad, proof of Proposition 2.1.6, pp. 62–63; the affine base-change
construction in Step 4 of (blueprint: lem-sfb-smooth-section-finite-jets).
This construction does not require smoothness or flatness. -/
def smoothSectionBaseChangeAugmentation
    (A B A' : Type u) [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] (ε : B →ₐ[A] A) : B ⊗[A] A' →ₐ[A] A' :=
  Algebra.TensorProduct.lift ((Algebra.ofId A A').comp ε) (AlgHom.id A A')
    (fun _ _ ↦ Commute.all _ _)

/-- Infinitesimal neighborhoods of a smooth affine section are finite locally free
and commute with arbitrary scalar extension, including their closed immersions.

Source: Conrad, Reductive group schemes, proof of Proposition 2.1.6, pp. 62–63.
(blueprint: lem-sfb-smooth-section-finite-jets)

Proof:
1. Affine local finite presentation and affine formal smoothness give a smooth
   ring map, using lem-weil-pbc-lfp-affine-opens-finite-presentation,
   lem-weil-pbc-affine-formally-smooth-iff-ring-lifting and
   lem-weil-pbc-fp-square-zero-lifting-smooth-ring-map.
2. Subtract the augmentation of each of finitely many algebra generators. The
   resulting generators generate J = ker ε, and monomials of degree below n+1
   span Q = B/J^(n+1) over A, so Q is finite as an A-module.
3. J^(n+1) is finitely generated. Apply
   lem-weil-pbc-finite-presentation-quotient-fg-ideal and
   lem-weil-pbc-finite-algebra-presentation-module-presentation to obtain finite
   presentation of Q as an algebra and then as a module.
4. After any base change, the identity obtained by subtracting the augmentation
   of each tensor factor shows ker ε' = J B'. Powers also commute with extension.
5. The maps [b] ⊗ a' ↦ [b ⊗ a'] and [b ⊗ a'] ↦ [b] ⊗ a' are well-defined
   and inverse. Their formulas give compatibility with the quotient maps.
6. Localize at a prime of A. Smoothness survives by
   lem-weil-pbc-smooth-ring-map-base-change-composition. Apply
   lem-sbc-smooth-augmentation-first-order-coordinates over the local base.
   The square-zero lifts of lem-weil-pbc-smooth-ring-map-square-zero-lifting
   give all nilpotent lifts by induction through successive powers of the ideal.
7. Apply lem-sbc-formally-smooth-augmentation-truncations. Monomials of degree
   below n+1 span the polynomial truncation and are independent: an element of
   the (n+1)st variables-ideal power has zero coefficients in all these degrees.
   There are finitely many such monomials, including when the rank or n is zero.
   Step 5 identifies this with the localization of Q.
8. Apply lem-trf-finite-projective-local-free to the finitely presented module Q,
   then lem-weil-pbc-projective-module-flat. The zero ring case holds directly.
9. The finite algebra Q defines a finite scheme morphism. Its finite algebra
   presentation gives local finite presentation; lem-weil-pbc-flat-local-ring-maps
   gives flatness on stalks. These are def-pc-finite-locally-free's three fields.
10. Apply lem-weil-pbc-fibre-product-affine-spectra and the equivalence of Step 5.
    The quotient compatibility identifies the closed immersions, and the algebra
    scalar compatibility identifies the projections to Spec A'. -/
theorem smooth_section_finite_jets
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Smooth (Spec.map (CommRingCat.ofHom (algebraMap A B)))]
    (ε : B →ₐ[A] A) (n : ℕ) :
    (Spec.map (CommRingCat.ofHom
      (algebraMap A (B ⧸ (RingHom.ker ε.toRingHom) ^ (n + 1))))).IsFiniteLocallyFree ∧
    ∀ (A' : Type u) [CommRing A'] [Algebra A A'],
      ∃ E : @AlgEquiv A'
          ((B ⧸ (RingHom.ker ε.toRingHom) ^ (n + 1)) ⊗[A] A')
          ((B ⊗[A] A') ⧸
            (RingHom.ker (smoothSectionBaseChangeAugmentation A B A' ε).toRingHom) ^ (n + 1))
          _ _ _ Algebra.TensorProduct.rightAlgebra
          (@Ideal.Quotient.algebra A' (B ⊗[A] A') _ _
            Algebra.TensorProduct.rightAlgebra _ _),
        (∀ (b : B) (a' : A'),
          E (Ideal.Quotient.mk ((RingHom.ker ε.toRingHom) ^ (n + 1)) b ⊗ₜ[A] a') =
            Ideal.Quotient.mk
              ((RingHom.ker
                (smoothSectionBaseChangeAugmentation A B A' ε).toRingHom) ^ (n + 1))
              (b ⊗ₜ[A] a')) ∧
        ∃ σ : pullback
            (Spec.map (CommRingCat.ofHom
              (algebraMap A (B ⧸ (RingHom.ker ε.toRingHom) ^ (n + 1)))))
            (Spec.map (CommRingCat.ofHom (algebraMap A A'))) ≅
              Spec (CommRingCat.of ((B ⊗[A] A') ⧸
                (RingHom.ker
                  (smoothSectionBaseChangeAugmentation A B A' ε).toRingHom) ^ (n + 1))),
          σ.hom ≫ Spec.map (CommRingCat.ofHom
            ((Ideal.Quotient.mk
              ((RingHom.ker
                (smoothSectionBaseChangeAugmentation A B A' ε).toRingHom) ^ (n + 1))).comp
              Algebra.TensorProduct.includeLeftRingHom)) =
            pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom
              (Ideal.Quotient.mk ((RingHom.ker ε.toRingHom) ^ (n + 1)))) ∧
          σ.hom ≫ Spec.map (CommRingCat.ofHom
            ((Ideal.Quotient.mk
              ((RingHom.ker
                (smoothSectionBaseChangeAugmentation A B A' ε).toRingHom) ^ (n + 1))).comp
              Algebra.TensorProduct.includeRight.toRingHom)) =
            pullback.snd _ _ := by
  sorry

end AlgebraicGeometry
