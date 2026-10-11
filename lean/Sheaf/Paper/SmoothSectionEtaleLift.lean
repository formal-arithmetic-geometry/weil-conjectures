/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
import Mathlib.Algebra.Category.CommAlgCat.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # Sections of smooth algebras modulo an ideal lift over an étale neighbourhood

Source: Stacks Project, More on Algebra, Lemma Tag 07M7
(blueprint: lem-weil-pbc-smooth-section-etale-lift).
-/

universe u

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry

/-- (blueprint: lem-weil-pbc-smooth-section-etale-lift)
Let `A` be a commutative ring, `J` an ideal, and `B` a smooth `A`-algebra.
Every `A`-algebra section of `B` to `A/J` lifts after an étale neighbourhood
of `A` inducing an isomorphism on the quotient.
Proof: Stacks Project, More on Algebra, Lemma 07M7
(`lemma-lift-section-smooth-morphism`). Follow the node's ten steps:
1. Use `lem-weil-pbc-smooth-ring-map-iff-smooth-affine` to pass to smooth ring maps.
   Set `N = ker σ`; surjectivity of the quotient gives `B/N ≅ A/J` and `JB ≤ N`.
2. By `lem-weil-pbc-smooth-conormal-sequence-exact`, the conormal sequence identifies
   `P = N/(N² + JB)` with the base change of the differentials, hence finite projective.
   The image of `J/J²` is `(JB + N²)/N²`, since each element of `B` lifts modulo `N`
   from `A`.
3. If `P` is free of rank `n`, lift a basis to `f₁, …, fₙ ∈ N` and form
   `C = B/(f₁, …, fₙ)`. It is finitely presented and `σ` factors through `C`.
4. `lem-weil-pbc-jacobi-zariski-quotient-smooth` gives the exact sequence from
   `H₁(L_{C/A})` through the conormal module and differentials to `Ω_{C/A}`.
5. At primes containing `NC`, the differential module is free of rank `n` by
   `lem-weil-pbc-finite-projective-rank-locally-constant`. Nakayama
   (`lem-weil-pbc-nakayama-local-generators`) makes the conormal map surjective.
   Its source has `n` generators; `lem-weil-pbc-finite-module-surjective-endomorphism-bijective`
   makes it an isomorphism. Both cotangent obstructions therefore vanish there.
6. `lem-weil-pbc-etale-near-prime-naive-cotangent-vanishing` and
   `lem-weil-pbc-etale-localize-upstairs` give an étale localization `C_h` with
   `h` invertible modulo `NC`, so the section extends to `C_h → A/J`.
7. By `lem-weil-pbc-etale-quotient-base-change` and
   `lem-weil-pbc-etale-section-idempotent-splitting`, localize `C_h/JC_h` at an
   idempotent to obtain `A/J`. Lift that idempotent to `g ∈ C_h` and set `A' = (C_h)_g`.
   `lem-weil-pbc-lift-invertible-element` and
   `lem-weil-pbc-etale-composition-cancellation` give étaleness. The resulting quotient
   isomorphism identifies the composite `B → A'` with `σ` modulo `J`.
8. If a finite projective `A`-module `Q` complements `P` modulo `J` to a free module,
   replace `B` by `B ⊗ Sym_A(Q)`, using
   `lem-weil-pbc-symmetric-algebra-universal-property`,
   `lem-weil-pbc-symmetric-algebra-finite-projective-smooth`, and
   `lem-weil-pbc-smooth-ring-map-base-change-composition`.
   Its conormal module is `P ⊕ Q/JQ`: the positive-degree augmentation ideal
   modulo its square contributes precisely `Q/JQ`. Apply the free case and restrict
   the resulting lift along `B → B ⊗ Sym_A(Q)`.
9. In general, choose a finite projective complement of `P` over `A/J` and lift it
   over an étale neighbourhood `A₁` by `lem-weil-pbc-lift-projective-module-etale`.
   Base change `B` and `σ` to `A₁`; smoothness persists, and
   `lem-weil-pbc-kahler-differentials-base-change` together with the conormal sequence
   identifies the new conormal module with the base change of `P`. Thus step 8 applies.
10. Compose the étale maps `A → A₁ → A'` using
    `lem-weil-pbc-etale-composition-cancellation`. Compose the quotient isomorphisms
    and restrict the lift to `B`; the quotient compatibility follows by composition.
-/
theorem exists_etale_lift_of_smooth
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal A) (σ : B →ₐ[A] A ⧸ J)
    (hB : Smooth (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A B)).op)) :
    ∃ (A' : CommAlgCat.{u} A),
      Etale (Scheme.Spec.map (CommRingCat.ofHom (algebraMap A A')).op) ∧
      ∃ (α : A ⧸ J →ₐ[A]
          A' ⧸ (J.map (algebraMap A A'))),
        Function.Bijective α ∧
        ∃ (tildeσ : B →ₐ[A] A'),
          Ideal.Quotient.mk (J.map (algebraMap A A')) ∘ tildeσ =
            α.toRingHom ∘ σ.toRingHom := by
  sorry

end AlgebraicGeometry
