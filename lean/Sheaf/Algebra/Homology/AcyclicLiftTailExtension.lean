/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# One-degree extension of an acyclic lift tail

Source: Stacks Project, Tag 0BC9, proof of lemma-lift-acyclic-complex.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace CochainComplex

/-- A finite lift tail, exact strictly above its left endpoint. All stored data are explicit;
no existence theorem is used to define this structure. -/
structure AcyclicLiftTail (R : Type u) [CommRing R] (I : Ideal R)
    (P : ModuleCat.{max u v} R → Prop)
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ) (b n : ℤ) where
  complex : CochainComplex (ModuleCat.{max u v} R) ℤ
  comparison : ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj complex ⟶ E
  lower : complex.IsStrictlyGE n
  upper : complex.IsStrictlyLE b
  terms : ∀ i, P (complex.X i)
  exact : ∀ i, n < i → complex.ExactAt i
  iso : ∀ i, n ≤ i → IsIso (comparison.f i)

/-- Extend a finite projective lift tail by one degree.

Source: Stacks Project, Tag 0BC9, proof, the split-tail and next-term construction
(blueprint: lem-sc-acyclic-lift-tail-extension).

Proof: Starting at degree b, split the surjections onto cycles using projectivity.
Descending through the finite tail identifies each term with the sum of its cycle
module and the next cycle module. The summand hypothesis puts all these cycle
modules in P (including the zero module). Choose a lift M in P of E in degree n-1.
The differential of E lands in the reduction of the cycle module Z in degree n:
the split tail remains split after reduction, and E is exact in degree n.
Projectivity of M lifts the resulting map M -> Z/IZ to M -> Z. Its reduction is
surjective, so the surjectivity hypothesis makes the lifted map surjective.
Compose it with the inclusion of Z in the degree-n term. Put M in degree n-1,
keep the old terms and differentials above n, and put zero below n-1. This is a
complex since the new map lands in cycles. It is exact in degree n and remains
exact above n. Its reduction comparison is the chosen isomorphism in degree n-1
and the previous comparison in all higher degrees. The inclusion of the old tail
commutes with this comparison and is an isomorphism in every degree at least n.
Every unchanged term belongs to P; the new term does by choice, and the lower
zero terms already occur in the old tail. -/
theorem exists_extend_acyclicLiftTail
    (R : Type u) [CommRing R] (I : Ideal R)
    (P : ModuleCat.{max u v} R → Prop)
    (hprojective : ∀ M, P M → Projective M)
    (hsummand : ∀ M₁ M₂ M₁₂ : ModuleCat.{max u v} R,
      P M₁ → P M₁₂ → Nonempty (M₁₂ ≅ ModuleCat.of R (M₁ × M₂)) → P M₂)
    (hsurjective : ∀ (M₁ M₂ : ModuleCat.{max u v} R) (f : M₁ ⟶ M₂),
      P M₁ → P M₂ →
      Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) →
      Function.Surjective f)
    (E : CochainComplex (ModuleCat.{max u v} (R ⧸ I)) ℤ)
    (hacyclic : E.Acyclic)
    (hterms : ∀ i : ℤ, ∃ M : ModuleCat.{max u v} R, P M ∧
      Nonempty ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj M ≅ E.X i))
    (b n : ℤ) (hn : n ≤ b + 1) (T : AcyclicLiftTail R I P E b n) :
    ∃ T' : AcyclicLiftTail R I P E b (n - 1),
      ∃ f : T.complex ⟶ T'.complex,
        (∀ i, n ≤ i → IsIso (f.f i)) ∧
        ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f ≫ T'.comparison = T.comparison := by sorry

end CochainComplex
