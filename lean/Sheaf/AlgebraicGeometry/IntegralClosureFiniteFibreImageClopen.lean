/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group J1
-/
module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-! # The finite fibre component has a clopen image in the integral closure

Source: literature/stacks-project/more-algebra.tex:2529-2541, proof of Lemma Tag 09XH
(blueprint: lem-weil-pbc-integral-closure-finite-fibre-image-clopen)
-/

@[expose] public section

universe u v w z

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

/-- The finite fibre component has a clopen image in the integral closure.

Source: literature/stacks-project/more-algebra.tex:2529-2541, proof of Lemma Tag 09XH
(blueprint: lem-weil-pbc-integral-closure-finite-fibre-image-clopen).

1. For a lift of the component idempotent, identify `T` with `V(IB) ∩ D(ε)` using
   lem-weil-pbc-spec-quotient-homeomorphism-zero-locus.
2. The inclusion carries `IB'` into `IB`, and the image of `I` generates both ideals;
   consequently the inverse image of `V(IB')` is `V(IB)`.
3. The isomorphism over `U` carries the principal open piece to an open piece, showing
   that the image of `T` is open in `V(IB')` (def-weil-affine-spectrum).
4. Finiteness of `C₁` over `A/I` gives integrality over `B'`, so the spectrum image is
   closed by lem-weil-pbc-finite-algebra-is-integral and lem-weil-pbc-integral-spec-closed-map.
5. Pull back along the quotient-spectrum homeomorphism and apply
   lem-weil-pbc-spec-clopen-idempotent to obtain the unique idempotent and product factors.
6. Injectivity over `U` shows that the inverse image of the image is precisely `T`.
7. The two idempotents have the same basic open after pullback. Uniqueness in
   lem-weil-pbc-spec-clopen-idempotent gives `f ε' = ε` and preservation of both factors.
8. Use lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact to choose a lift `g` of `ε'`
   with `D(g) ⊆ U`, by separating the closed complement of `U` from the first factor.
9. On `D(g)` the isomorphism of locally ringed spaces identifies the section rings,
   hence the localizations `B'_g` and `B_g` (lem-weil-pbc-morphism-into-affine-scheme,
   lem-weil-pbc-affine-ideals-closed-subscheme, def-weil-ring-localization-away).
10. Quotient this localization isomorphism by the corresponding ideals `(I, 1-g)`;
    these quotient rings are the first factors, and the induced first-factor map is
    therefore a ring isomorphism. -/
theorem integralClosure_finiteFibre_image_clopen
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (I : Ideal A)
    {C₁ : Type w} {C₂ : Type z} [CommRing C₁] [CommRing C₂]
    [Algebra (A ⧸ I) C₁] [Module.Finite (A ⧸ I) C₁]
    (e : (B ⧸ Ideal.map (algebraMap A B) I) ≃+* C₁ × C₂)
    (hcompat : ∀ a : A, algebraMap (A ⧸ I) C₁ (Ideal.Quotient.mk I a) =
      (e (Ideal.Quotient.mk _ (algebraMap A B a))).1)
    (U : (Spec (.of (integralClosure A B))).Opens)
    (hiso : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap (integralClosure A B) B)) ∣_ U)) :
    let R := B ⧸ Ideal.map (algebraMap A B) I
    let R' := (integralClosure A B) ⧸ Ideal.map (algebraMap A (integralClosure A B)) I
    let π := Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)
    let π' := Ideal.Quotient.mk (Ideal.map (algebraMap A (integralClosure A B)) I)
    let ι := algebraMap (integralClosure A B) B
    let φ := PrimeSpectrum.comap ι
    let β := (RingHom.fst C₁ C₂).comp (e.toRingHom.comp π)
    let T := Set.range (PrimeSpectrum.comap β)
    T ⊆ φ ⁻¹' U.1 →
      ∃ (f : R' →+* R),
        (∀ b, f (π' b) = π (ι b)) ∧
        IsClopen ((PrimeSpectrum.comap π') ⁻¹' (φ '' T)) ∧
        φ ⁻¹' (φ '' T) = T ∧
        ∃ (ε' : R'), IsIdempotentElem ε' ∧
          φ '' T = PrimeSpectrum.comap π' '' (PrimeSpectrum.basicOpen ε' : Set _) ∧
          (∀ δ : R', IsIdempotentElem δ →
            φ '' T = PrimeSpectrum.comap π' '' (PrimeSpectrum.basicOpen δ : Set _) →
            δ = ε') ∧
          f ε' = e.symm (1, 0) ∧
          ∃ (C'₁ C'₂ : Type u) (_ : CommRing C'₁) (_ : CommRing C'₂)
            (e' : R' ≃+* C'₁ × C'₂) (g : C'₁ ≃+* C₁) (h : C'₂ →+* C₂),
            e' ε' = (1, 0) ∧
            ∀ r : R', e (f r) = (g (e' r).1, h (e' r).2) := by
  sorry

end AlgebraicGeometry
