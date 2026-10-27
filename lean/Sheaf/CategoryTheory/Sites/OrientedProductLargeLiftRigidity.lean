/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P8
-/
module

public import Sheaf.CategoryTheory.Sites.OrientedProductLargeSiteData

/-! # Rigidity of compatible lifts to the large triple site

Source: ILO Exposé XI Lemma 1.5 and §1.6.
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

/-- Every compatible lift satisfies the pullback formula, and two such lifts have a
unique projection-compatible isomorphism.

Source: ILO XI Lemma 1.5 and §1.6, uniqueness in Theorem 1.4
(blueprint: lem-trf-large-oriented-lift-rigidity).

For Z=(U,V,W), form C=(U,V,GV) and D=(FV,V,W). Componentwise pullbacks give
D=T_V ×_(e,e,GV) (e,e,W) and Z=C ×_T_V D. The maps C→(U,e,e) and
T_V→(FV,e,e) are of type (c). Associated representables preserve these pullbacks;
sheafification is left exact and makes these two arrows invertible. This gives
the asserted pullback square of sheaves. A compatible geometric inverse image
preserves the square, and mate compatibility identifies its bottom maps with
the maps induced by t. Two lifts therefore have uniquely isomorphic restrictions
to associated representables, compatible with the two projections. The proved theorem
largeDirectImageFromRepresentables extends the isomorphism and its inverse uniquely
to the direct images. Its uniqueness makes both composites identities. The same
section calculation forces equality of any other projection-compatible comparison.
-/
theorem largeCompatibleLiftRigidity
    (hτ : LargeOrientationFormula F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ) :
    LargeHasLiftFormula.{v, w, e, ve} F G J₁ J₂ K f g ηF ηG p₁ p₂ π₁ π₂ τ ∧
    ∀ (E : Type e) [Category.{ve} E], IsGrothendieckTopos.{max v w} E →
      ∀ (a : GeometricMorphism E (Sheaf J₁.toGrothendieck (Type (max v w))))
        (b : GeometricMorphism E (Sheaf J₂.toGrothendieck (Type (max v w))))
        (t : (b.comp g).direct ⟶ (a.comp f).direct)
        (h h' : GeometricMorphism E (Sheaf (largeTopology J₁ J₂ F G) (Type (max v w))))
        (α : (h.comp p₁).direct ≅ a.direct) (β : (h.comp p₂).direct ≅ b.direct)
        (α' : (h'.comp p₁).direct ≅ a.direct) (β' : (h'.comp p₂).direct ≅ b.direct),
        paste f g p₁ p₂ τ h a b α β = t →
        paste f g p₁ p₂ τ h' a b α' β' = t →
        ∃! γ : h.direct ≅ h'.direct,
          Functor.isoWhiskerRight γ p₁.direct ≪≫ α' = α ∧
          Functor.isoWhiskerRight γ p₂.direct ≪≫ β' = β := by sorry

end CategoryTheory.OrientedProduct
