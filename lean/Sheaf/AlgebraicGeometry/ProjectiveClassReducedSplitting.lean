/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-! # Lifting reduced splittings in a projective class

Source: Stacks Project, More on Algebra, Tag 0BCA.
-/

@[expose] public section

universe u v

open CategoryTheory

namespace AlgebraicGeometry

/-- Lift a split reduced right-exact sequence for a projective class.

Source: Stacks Project, More on Algebra, Tag 0BCA, final paragraph.
(blueprint: lem-sc-projective-class-reduced-splitting).

Proof: Choose a class member T lifting the last reduced module. Lift the reduced
projection from the middle term to T using projectivity of the middle term. It is
surjective by the class hypothesis and splits by projectivity of T. Its kernel U
belongs to the class by closure under summands. The composite from the first term
into U is invertible modulo I, hence is surjective and splits. Its kernel V belongs
to the class and has zero reduction. The zero module belongs to the class as a
summand of the first term; apply the surjectivity hypothesis to zero -> V to get
V = 0. Thus the composite into U is invertible and the original first map is a
split injection. Exactness and epimorphy identify the last term with its cokernel.
The resulting decomposition of the middle term, and the class condition, put this
cokernel in the class. -/
theorem projective_class_reduced_splitting
    (R : Type u) [CommRing R] (I : Ideal R)
    (Pclass : Set (ModuleCat.{max u v} R))
    (hproj : ∀ P : ModuleCat.{max u v} R, P ∈ Pclass → Projective P)
    (hclosed : ∀ P₁ P₂ P₁₂ : ModuleCat.{max u v} R,
      Nonempty (P₁₂ ≅ ModuleCat.of R (P₁ × P₂)) →
      (P₁ ∈ Pclass ∧ P₁₂ ∈ Pclass ↔ P₁ ∈ Pclass ∧ P₂ ∈ Pclass))
    (hsurj : ∀ (P₁ P₂ : ModuleCat.{max u v} R) (f : P₁ ⟶ P₂),
      P₁ ∈ Pclass → P₂ ∈ Pclass →
      Function.Surjective ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).map f) →
      Function.Surjective f)
    (S : ShortComplex (ModuleCat.{max u v} R))
    (hexact : S.Exact) (hepi : Epi S.g)
    (hfirst : S.X₁ ∈ Pclass) (hmiddle : S.X₂ ∈ Pclass)
    (hsplit : Nonempty ((S.map (ModuleCat.extendScalars (Ideal.Quotient.mk I))).Splitting))
    (hlast : ∃ P : ModuleCat.{max u v} R, P ∈ Pclass ∧
      Nonempty ((ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj S.X₃ ≅
        (ModuleCat.extendScalars (Ideal.Quotient.mk I)).obj P)) :
    S.ShortExact ∧ S.X₃ ∈ Pclass := by
  sorry

end AlgebraicGeometry
