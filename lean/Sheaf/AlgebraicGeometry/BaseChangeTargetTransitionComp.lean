/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.SixFunctors.Etale.SmoothBaseChange.FailureOverField.Transition
import Sheaf.AlgebraicGeometry.DerivedInverseImageComposition

/-! # Composition of target transitions

Source: the transition argument in Stacks Tag 0F07, thickening step.
(blueprint: lem-sbc-target-transition-comp)
-/

@[expose] public section

universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry
variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Target transitions compose, including the comparison of the coefficient pullbacks.

Source: Stacks Tag 0F07, proof of condition (1), and the definition of the canonical
restriction maps in Tag 09Z1. (blueprint: lem-sbc-target-transition-comp)

Proof: expand the transitions as derived units and counits. Paste the two degenerate
commutative squares using the generic mate-pasting law (which requires no cartesianness);
the triangle identities identify their composite
with the transition for the composite. The associativity of the pullback comparison
identifies the final coefficient with `(π₁ ≫ π₂)^* F`. Apply degree-q homology.
-/
theorem Etale.baseChangeTargetTransition_comp
    {X T Y T₁ T₂ Y₁ Y₂ : Scheme.{u}} (e : Y ⟶ T) (h : Y ⟶ X) (q : ℤ)
    (π₂ : T₂ ⟶ T) (a₂ : Y₂ ⟶ Y) (e₂ : Y₂ ⟶ T₂) (h₂ : Y₂ ⟶ X)
    (wa₂ : a₂ ≫ e = e₂ ≫ π₂) (wh₂ : a₂ ≫ h = h₂)
    (π₁ : T₁ ⟶ T₂) (a₁ : Y₁ ⟶ Y₂) (e₁ : Y₁ ⟶ T₁) (h₁ : Y₁ ⟶ X)
    (wa₁ : a₁ ≫ e₂ = e₁ ≫ π₁) (wh₁ : a₁ ≫ h₂ = h₁)
    (F : Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Etale.baseChangeTargetTransition Λ e h q π₂ a₂ e₂ h₂ wa₂ wh₂ F ≫
        Etale.baseChangeTargetTransition Λ e₂ h₂ q π₁ a₁ e₁ h₁ wa₁ wh₁
          (((π₂)^*[ModuleCat.{u + 1} Λ]).obj F) ≫
        (Etale.baseChangeTargetFunctor Λ e₁ h₁ q).map
          ((Etale.upperStarComp (ModuleCat.{u + 1} Λ) π₁ π₂ (π₁ ≫ π₂) rfl).inv.app F) =
      Etale.baseChangeTargetTransition Λ e h q (π₁ ≫ π₂) (a₁ ≫ a₂) e₁ h₁
        (by rw [Category.assoc, wa₂, ← Category.assoc, wa₁, Category.assoc])
        (by rw [Category.assoc, wh₂, wh₁]) F := by sorry

end AlgebraicGeometry
