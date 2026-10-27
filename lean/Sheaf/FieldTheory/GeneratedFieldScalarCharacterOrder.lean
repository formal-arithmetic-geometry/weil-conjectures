/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q154
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.Algebra.Group.Subgroup.Defs
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.SetTheory.Cardinal.NatCard

import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fintype.EquivFin

/-!
# Scalar characters on a finite field-generating family

Source: Stacks Project, Fields, Tag 09I6, section Kummer extensions, opening paragraph;
the scalar-character and subgroup-order argument extended to a finite generating family
(blueprint: lem-sfb-generated-field-scalar-character-order).
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace AlgEquiv

/-- Automorphisms acting by scalars in a finite subgroup of the base-field units on a
field-generating family admit a unique scalar character. It is injective, so the
finite automorphism-group order divides the scalar-group order to the family size.
No algebraicity, normality or separability hypothesis is needed, and `r = 0` is allowed.

Source: Stacks Project, Fields, Tag 09I6, section Kummer extensions, opening paragraph,
extended to a finite list (blueprint: lem-sfb-generated-field-scalar-character-order).

Proof:
1. For each automorphism and generator, choose the scalar supplied by `hscalar`.
   Cancellation by the nonzero generator and injectivity of the base-field map show
   that this scalar is unique. Identity has scalar one. In a composite, the first
   automorphism fixes the second scalar because it lies in the base field. Thus
   coordinate scalars multiply, giving a group homomorphism to the tuple group.
   The same cancellation proves uniqueness among all homomorphisms with the formula.
2. If two characters agree, the automorphisms agree on each generator. Their equalizer
   is a subfield containing the image of the base field and all generators: closure
   follows from preservation of addition, negation, multiplication and inverses.
   The field-generating hypothesis makes this equalizer the whole field, proving
   injectivity of the character.
3. The tuple group is finite of order `Nat.card U ^ r`, by counting finite products
   (including the singleton empty product). Apply `Finite.of_injective` and
   `Subgroup.card_dvd_of_injective`, the two clauses of
   `lem-sfb-injective-hom-finite-group-order`, to the character. This gives finiteness
   and divisibility. When `r = 0`, the generating hypothesis says that the base-field
   image is the whole field; the injection into the empty-tuple group also shows
   that the automorphism group is trivial. -/
theorem generated_field_scalar_character_order
    (F : Type u) [Field F] (E : Type v) [Field E] [Algebra F E]
    (r : ℕ) (b : Fin r → Eˣ)
    (hgen : IntermediateField.adjoin F (Set.range (fun j : Fin r ↦ (b j : E))) = ⊤)
    (U : Subgroup Fˣ) [Finite U]
    (hscalar : ∀ (σ : E ≃ₐ[F] E) (j : Fin r),
      ∃ a : U, σ (b j : E) = algebraMap F E ((a : Fˣ) : F) * (b j : E)) :
    ∃ χ : (E ≃ₐ[F] E) →* (Fin r → U),
      (∀ (σ : E ≃ₐ[F] E) (j : Fin r),
        σ (b j : E) = algebraMap F E ((χ σ j : Fˣ) : F) * (b j : E)) ∧
      (∀ ψ : (E ≃ₐ[F] E) →* (Fin r → U),
        (∀ (σ : E ≃ₐ[F] E) (j : Fin r),
          σ (b j : E) = algebraMap F E ((ψ σ j : Fˣ) : F) * (b j : E)) → ψ = χ) ∧
      Function.Injective χ ∧ Finite (E ≃ₐ[F] E) ∧
      Nat.card (E ≃ₐ[F] E) ∣ Nat.card U ^ r := by
  sorry

end AlgEquiv
