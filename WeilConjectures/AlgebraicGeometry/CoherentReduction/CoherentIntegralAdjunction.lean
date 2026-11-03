/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.CoherentReduction.CoherentIntegralCompletionHom
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Equivalence

/-! # Combining the integral mapping comparisons into an adjunction

Source: the last paragraph of the proof of
`lem-sfb-dc-proper-pushforward-left-adjoint-oe`.
(blueprint: lem-sfb-coherent-integral-adjunction)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
universe u vC uC vD uD
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CoherentReduction
attribute [local instance] proEtSmall sequenceSmall

/-- A natural isomorphism between the two Hom bifunctors gives the adjunction.
Source: the natural Hom-bijection criterion, Stacks 0036
(blueprint: lem-sfb-coherent-integral-adjunction). -/
def adjunctionOfHomPairs
    {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vC} D]
    (F : C ⥤ D) (G : D ⥤ C)
    (e : F.op.prod (𝟭 D) ⋙ homPairs D ≅
      (𝟭 Cᵒᵖ).prod G ⋙ homPairs C) : F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y ↦ (e.app (op X, Y)).toEquiv
      homEquiv_naturality_left_symm := by
        intro X' X Y f g
        simpa [homPairs] using ConcreteCategory.congr_hom
          (e.inv.naturality (show (op X, Y) ⟶ (op X', Y) from (f.op, 𝟙 Y))) g
      homEquiv_naturality_right := by
        intro X Y Y' f g
        simpa [homPairs] using ConcreteCategory.congr_hom
          (e.hom.naturality (show (op X, Y) ⟶ (op X, Y') from (𝟙 _, g))) f }

end AlgebraicGeometry.ProEtale.CoherentReduction
