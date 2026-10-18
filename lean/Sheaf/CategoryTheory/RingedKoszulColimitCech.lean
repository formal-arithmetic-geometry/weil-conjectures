/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H1
-/
module

public import Sheaf.CategoryTheory.RingedKoszulSystem

/-! # The augmented finite Koszul colimit

Source: Stacks Project, Tag 0913. -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable (O : Sheaf J CommRingCat.{u}) (r : ℕ)
variable (b : Fin r → (O.obj ⋙ forget CommRingCat).sections)

/-- The ordered positive Koszul system has the augmented localization complex as colimit.
Source: Stacks Project, More on Algebra, Tag 0913.
(blueprint: lem-weil-pbc-ringed-koszul-colimit-cech).

Proof: for a subset I put t_I equal to the product of its sections. In its summand send
an element a at stage m to a/t_I^(m+1). Multiplication by t_I is the transition, so
these maps are compatible. Every fraction occurs and equality of two fractions means
equality at a later stage. Sheafification gives the same colimit of module sheaves.
Insertion of j multiplies the numerator by b_j^(m+1), which cancels that factor in
the denominator and gives the alternating localization differential. The empty subset
has t_I=1 and the constant degree-zero summand; hence the projection to O[0] agrees.
For no sections both diagrams are the constant degree-zero ring complex. -/
theorem ringedKoszul_colimit_cech :
    ∃ alpha : colimit (ringedKoszulDiagram O r b) ≅ (ringedExtendedCech O r b).1,
      alpha.hom ≫ (ringedExtendedCech O r b).2 =
        colimit.desc _ (ringedKoszulAugmentationCocone O r b) := by sorry

end CategoryTheory
