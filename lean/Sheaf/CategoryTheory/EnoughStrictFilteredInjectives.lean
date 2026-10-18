/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
-/
module

public import Sheaf.CategoryTheory.Filtration
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import Sheaf.CategoryTheory.InjectiveGradedFiltrationSplits
import WeilConjectures.CategoryTheory.Abelian.Filtration

/-!
# Enough injectives for strict finite filtered objects

Source: Stacks Project, `derived.tex`, Tags 05TR and 05TS
(blueprint: lem-trf-enough-strict-filtered-injectives).

The first clause is proved componentwise after splitting a finite filtered
injective into its injective graded pieces (the split description is the
statement of `lem-trf-injective-graded-filtration-splits`).  Strictness makes
the induced maps on the successive quotients monomorphisms, so the ordinary
injective extension property applies to each component.  Under
`EnoughInjectives`, the second clause embeds each quotient into an injective,
assembles the finite biproduct with the split filtration, and checks
monicity and strictness by the last nonzero coordinate and the lower-coordinate
projection.  The same construction gives the prescribed interval bounds,
including the zero and one-step cases.
-/

@[expose] public section

set_option autoImplicit false
set_option warn.sorry false

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.FilteredObject

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Finite filtered objects have enough filtered injectives for strict monomorphisms.
Source: Stacks Project, `derived.tex`, Tags 05TR and 05TS
(blueprint: lem-trf-enough-strict-filtered-injectives).

Proof plan:
1. Split a finite filtered injective into a finite biproduct of injective graded
   pieces using `lem-trf-injective-graded-filtration-splits`; the component of a
   filtered map to the `n`-th summand kills the next filtration step.
2. Strictness identifies the kernel of the map on each quotient
   `X/F^(n+1)X → Y/F^(n+1)Y` with zero, so the component factors through a
   monomorphism of quotients.
3. Extend each component by ordinary injectivity and assemble the finite
   biproduct map; the decreasing filtration makes all components below the
   filtration index vanish, so the result is filtered.
4. Assuming `EnoughInjectives`, embed every quotient of a finite filtered object
   into an injective, and use their finite biproduct with the split filtration.
5. The final coordinate proves monicity; the projection to coordinates below a
   given index has kernel exactly the corresponding filtration step, proving
   strictness and preserving the prescribed bounds. -/
theorem enough_strict_filtered_injectives :
    (∀ {X Y I : FilteredObject C}
      (hX : X.filtration.IsFinite) (hY : Y.filtration.IsFinite)
      (hI : I.filtration.IsFinite) (u : X ⟶ Y) [Mono u.hom],
      (∀ p : ℤ,
        imageSubobject ((X.filtration.step p).arrow ≫ u.hom) =
          imageSubobject u.hom ⊓ Y.filtration.step p) →
      (∀ p : ℤ, Injective (I.filtration.gradedPiece p)) →
      ∀ f : X ⟶ I, ∃ g : Y ⟶ I, u ≫ g = f) ∧
    (EnoughInjectives C →
      ∀ X : FilteredObject C,
        X.filtration.IsFinite →
        ∃ (I : FilteredObject C) (v : X ⟶ I),
          I.filtration.IsFinite ∧ Mono v.hom ∧
            (∀ p : ℤ,
              imageSubobject ((X.filtration.step p).arrow ≫ v.hom) =
                imageSubobject v.hom ⊓ I.filtration.step p) ∧
            (∀ p : ℤ, Injective (I.filtration.gradedPiece p))) ∧
    (EnoughInjectives C →
      ∀ (X : FilteredObject C) (a b : ℤ), a ≤ b →
        X.filtration.step a = ⊤ → X.filtration.step (b + 1) = ⊥ →
        ∃ (I : FilteredObject C) (v : X ⟶ I),
          Mono v.hom ∧
            (∀ p : ℤ,
              imageSubobject ((X.filtration.step p).arrow ≫ v.hom) =
                imageSubobject v.hom ⊓ I.filtration.step p) ∧
            (∀ p : ℤ, Injective (I.filtration.gradedPiece p)) ∧
            I.filtration.step a = ⊤ ∧ I.filtration.step (b + 1) = ⊥) := by
  sorry

end CategoryTheory.FilteredObject

end
