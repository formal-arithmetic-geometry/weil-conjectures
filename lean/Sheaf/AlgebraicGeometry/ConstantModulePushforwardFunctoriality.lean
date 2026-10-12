/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

/-!
# Functorial maps between direct images of constant modules

Source: Stacks Project, Tag 09Z1, canonical transition maps.
(blueprint: lem-weil-pbc-constant-module-pushforward-functoriality).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Etale

/-- Pull back constant-module sections along a morphism over the base, using the
inverse-image adjunction and its canonical constant-sheaf comparison. -/
noncomputable def constantModulePushforwardMap
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ)
    {X Y₁ Y₂ : Scheme.{u}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X)
    (g : Y₂ ⟶ Y₁) (h : g ≫ f₁ = f₂) :
    (lowerStar (ModuleCat.{u + 1} Λ) f₁).obj
        ((constantSheaf Y₁.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) ⟶
      (lowerStar (ModuleCat.{u + 1} Λ) f₂).obj
        ((constantSheaf Y₂.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj M) :=
  (lowerStar (ModuleCat.{u + 1} Λ) f₁).map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) g).map
          ((Scheme.upperStarConstantSheafIso (ModuleCat.{u + 1} Λ) g).hom.app M)) ≫
    (lowerStarComp (ModuleCat.{u + 1} Λ) g f₁ f₂ h.symm).hom.app _

/-- The canonical constant-module pushforward maps preserve identity and composition
contravariantly in the scheme over the base.

Source: Stacks Project, Tag 09Z1, system of sheaves and its direct-image transitions;
Tag 09Z6, finite approximation paragraph.
(blueprint: lem-weil-pbc-constant-module-pushforward-functoriality).

Proof: The map adjoint to the canonical pullback comparison sends a constant section
with value m to the constant section with value m. On an etale object of the base,
its direct image is restriction along the induced map of fibre products. Restriction
along the identity is the identity; restriction along a composite is the composite
of restrictions in reverse order. These equalities hold on constant presheaves and
extend uniquely to their sheafifications. The inverse-image adjunction identifies
these restrictions with the displayed maps. The lowerStar composition comparisons
are precisely the fibre-product pasting comparisons, so these sectionwise identities
prove both asserted equalities. This applies also to zero modules and empty schemes. -/
theorem constantModulePushforwardMap_id_comp
    (Λ : Type (u + 1)) [CommRing Λ] (M : ModuleCat.{u + 1} Λ) :
    (∀ {X Y : Scheme.{u}} (f : Y ⟶ X),
      constantModulePushforwardMap Λ M f f (𝟙 Y) (Category.id_comp f) = 𝟙 _) ∧
    (∀ {X Y₁ Y₂ Y₃ : Scheme.{u}} (f₁ : Y₁ ⟶ X) (f₂ : Y₂ ⟶ X) (f₃ : Y₃ ⟶ X)
      (g : Y₂ ⟶ Y₁) (g' : Y₃ ⟶ Y₂) (h : g ≫ f₁ = f₂) (h' : g' ≫ f₂ = f₃),
      constantModulePushforwardMap Λ M f₁ f₃ (g' ≫ g)
          (by rw [Category.assoc, h, h']) =
        constantModulePushforwardMap Λ M f₁ f₂ g h ≫
          constantModulePushforwardMap Λ M f₂ f₃ g' h') := by sorry

end AlgebraicGeometry.Etale
