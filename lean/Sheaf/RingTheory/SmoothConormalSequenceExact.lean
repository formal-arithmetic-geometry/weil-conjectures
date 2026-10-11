/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
import Mathlib.RingTheory.Smooth.Basic

/-!
# Exactness of the conormal sequence for a smooth ring map

Source: Stacks Project, Algebra, Tags 06A9 and 065V
(blueprint: lem-weil-pbc-smooth-conormal-sequence-exact).
-/

universe u v w

namespace Algebra.Extension

/-- Stacks Project, Algebra, Tag 06A9, with the maps of Tag 065V
(blueprint: lem-weil-pbc-smooth-conormal-sequence-exact).
The algebra structures encode `A → B → C`, and the scalar tower encodes commutativity.
The extensions `ofSurjective` have conormal modules `I/I²` and `J/J²` with their canonical
`C`-module structures. The generator equation uniquely specifies the induced map `u`.
The second map is `cotangentComplex`, sending a class of `b ∈ J` to `1 ⊗ db` in
`C ⊗[B] Ω[B⁄A]`; tensor symmetry identifies this with `db ⊗ 1` in the node.

Proof for stage 3:
1. The structure map takes `I` into `J` and `I²` into `J²`, inducing the `C`-linear `u`.
   Leibniz makes `b ↦ db ⊗ 1` vanish on `J²` and descend to the `C`-linear `v`.
   The universal derivation vanishes on `A`, so `v ∘ u = 0`
   (def-weil-pbc-kahler-differentials). For each `b ∈ B`, choose `a ∈ A` with the same
   image in `C`; then `b - φ(a) ∈ J` has differential `db`, so `v` is surjective.
   Surjectivity of `A → C` also implies surjectivity of `B → C`.
2. Smoothness implies formal smoothness (def-weil-pbc-smooth-ring-map). Apply
   lem-weil-pbc-smooth-ring-map-square-zero-lifting to `A/I² → C`, with square-zero
   kernel `I/I²`, obtaining an `A`-algebra map `σ : B → A/I²` lifting `B → C`.
3. On `J`, `σ` lands in `I/I²` and kills `J²`. It induces a `C`-linear map `r` with
   `r ∘ u = id`, since `σ(φ(a)) = a mod I²`. Thus `u` is injective (Tag 06A7).
4. Let `ι : A/I² → B/J²` be induced by `φ`. The difference
   `δ(b) = b mod J² - ι(σ(b))` is an `A`-derivation into `J/J²`. Its universal
   factorization gives `s : Ω[B⁄A] ⊗[B] C → J/J²`
   (def-weil-pbc-kahler-differentials), and `s(v(x)) = x - u(r(x))`.
   Therefore `v(x) = 0` implies `x = u(r(x))`; with step 1 this gives `ker v = im u`.
5. Injectivity from step 3, middle exactness from step 4, and surjectivity from step 1
   give the claimed exact sequence. -/
theorem smooth_conormal_sequence_exact
    {A : Type u} {B : Type v} {C : Type w}
    [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
    [Algebra.Smooth A B] (hπ : Function.Surjective (algebraMap A C)) :
    ∃ hβ : Function.Surjective (IsScalarTower.toAlgHom A B C),
      ∃ u : (ofSurjective (Algebra.ofId A C) hπ).Cotangent →ₗ[C]
          (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).Cotangent,
        (∀ (a : (ofSurjective (Algebra.ofId A C) hπ).ker)
          (b : (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).ker),
          (b.1 : B) = algebraMap A B (a.1 : A) →
            u (Cotangent.mk a) = Cotangent.mk b) ∧
        Function.Injective u ∧
        Function.Exact u
          (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).cotangentComplex ∧
        Function.Surjective
          (ofSurjective (IsScalarTower.toAlgHom A B C) hβ).cotangentComplex := by
  sorry

end Algebra.Extension
