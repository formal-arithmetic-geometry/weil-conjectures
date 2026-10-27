/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module

public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSiteData

/-! # Existence of compatible lifts to the large triple site

Source: ILO Exposé XI §1.6.
-/

@[expose] public section
set_option autoImplicit false
universe v w e ve
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory.OrientedProduct

variable {C₁ C₂ D : Type w} [Category.{v} C₁] [Category.{v} C₂] [Category.{v} D]
  [HasFiniteLimits C₁] [HasFiniteLimits C₂] [HasFiniteLimits D]
  (F : D ⥤ C₁) (G : D ⥤ C₂)
  [PreservesFiniteLimits F] [PreservesFiniteLimits G]

variable (J₁ : Pretopology C₁) (J₂ : Pretopology C₂) (K : Pretopology D)
    (f : GeometricMorphism (Sheaf J₁.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (g : GeometricMorphism (Sheaf J₂.toGrothendieck (Type (max v w)))
      (Sheaf K.toGrothendieck (Type (max v w))))
    (ηF : largeAssociated K.toGrothendieck ⋙ f.inverse ≅
      F ⋙ largeAssociated J₁.toGrothendieck)
    (ηG : largeAssociated K.toGrothendieck ⋙ g.inverse ≅
      G ⋙ largeAssociated J₂.toGrothendieck)
    (p₁ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₁.toGrothendieck (Type (max v w))))
    (p₂ : GeometricMorphism (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w)))
      (Sheaf J₂.toGrothendieck (Type (max v w))))
    (π₁ : largeAssociated J₁.toGrothendieck ⋙ p₁.inverse ≅
      largeFirst F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
    (π₂ : largeAssociated J₂.toGrothendieck ⋙ p₂.inverse ≅
      largeSecond F G ⋙ largeAssociated (largeTopology J₁ J₂ F G))
    (τ : (p₂.comp g).direct ⟶ (p₁.comp f).direct)

/-- Existence of a compatible lift of an oriented cone to the triple topos.

Source: ILO XI §1.6, formula (1.a), and Stacks Project Tags 00X6, 03A1, 03CI
(blueprint: lem-trf-large-oriented-lift-existence).

For (a,b,t), assign to a triple Z the pullback of a⁻¹(U) and b⁻¹(W) over
(gb)⁻¹(V), using the mate of t on the first factor. Naturality defines the
functor on arrows. Finite limits commute with pullbacks, so it is left exact.
Covers of types (a) and (b) map to jointly epimorphic families by base change.
A type-(c) arrow maps to an isomorphism by pullback cancellation and naturality
of the mate of t. Enlarge a presenting site of E by these objects and finite
limits; the site of generators and the site inverse-image theorem extend this
functor to a geometric inverse image. Evaluation at the first and second triples
gives the projection isomorphisms. Evaluation at the middle triples recovers t;
density of associated representables gives equality on all sheaves.
-/
theorem largeCompatibleLiftExists
    [F.IsContinuous K.toGrothendieck J₁.toGrothendieck]
    [G.IsContinuous K.toGrothendieck J₂.toGrothendieck]
    (hτ : LargeOrientationFormula F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ)
    (E : Type e) [Category.{ve} E] (hE : IsGrothendieckTopos.{max v w} E)
    (a : GeometricMorphism E (Sheaf J₁.toGrothendieck (Type (max v w))))
    (b : GeometricMorphism E (Sheaf J₂.toGrothendieck (Type (max v w))))
    (t : (b.comp g).direct ⟶ (a.comp f).direct) :
    ∃ (h : GeometricMorphism E (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w))))
      (α : (h.comp p₁).direct ≅ a.direct) (β : (h.comp p₂).direct ≅ b.direct),
      paste f g p₁ p₂ τ h a b α β = t := by sorry

end CategoryTheory.OrientedProduct
