/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.TotalSimplicialEtaleSite
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.Mathlib.CategoryTheory.Functor.KanExtension.Pointwise
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Functor.KanExtension.Adjunction
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-!
# The canonical augmentation of the total small étale site

Source: Stacks Project, Tags 0D70 and 0D99, the augmentation of simplicial sites
(blueprint: def-trf-total-etale-augmentation-adjunction).

The direct image is the right Kan extension from the total category to schemes over
its augmentation, restricted to étale objects. Its sections over `V` are the compatible
sections over all total objects mapping to `V`. This specifies the direct image on
objects and arrows before any adjoint is chosen. The inverse image is its left adjoint,
uniquely determined up to the unique adjunction-compatible isomorphism.

## Main definitions

- `totalEtaleToOver`: the actual structural functor to schemes over the base.
- `totalEtaleAugmentationDirect`: compatible sections, via right Kan extension.
- `totalEtaleAugmentationInverse`: the left adjoint characterized by this direct image.
- `totalEtaleAugmentationAdjunction`: the ordinary adjunction used to normalize the unit.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Forget an étale total object to its composite structural map to the base scheme.
Source: Stacks Project, Tags 09WC and 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction). -/
def totalEtaleToOver {X : Scheme.{u}} (U : SimplicialObject (Over X)) :
    TotalEtaleSite (U ⋙ Over.forget X) ⥤ Over X where
  obj W := Over.mk (W.obj.hom ≫ (U.obj W.obj.right).hom)
  map {W Z} f := Over.homMk f.hom.left (by
    change f.hom.left ≫ Z.obj.hom ≫ (U.obj Z.obj.right).hom =
      W.obj.hom ≫ (U.obj W.obj.right).hom
    have h : f.hom.left ≫ Z.obj.hom = W.obj.hom ≫ (U.map f.hom.right).left := f.hom.w
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun k ↦ k ≫ (U.obj Z.obj.right).hom) h).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k ↦ W.obj.hom ≫ k) (Over.w (U.map f.hom.right))))))

/-- The ordinary augmentation direct image before the sheaf condition is imposed.
Its right Kan extension is the limit of sections over total objects above a test scheme.
Source: Stacks Project, Tags 0D70 and 0D99
(blueprint: def-trf-total-etale-augmentation-adjunction). -/
def totalEtaleAugmentationDirectPresheaf {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    Sheaf (totalEtaleTopology (U ⋙ Over.forget X)) (ModuleCat.{u + 1} Λ) ⥤
      X.Etaleᵒᵖ ⥤ ModuleCat.{u + 1} Λ :=
  sheafToPresheaf _ _ ⋙ (totalEtaleToOver U).op.ran ⋙
    (Functor.whiskeringLeft _ _ _).obj (Scheme.Etale.forget X).op

/-- The compatible-section presheaf is an étale sheaf.
Source: Stacks Project, Tag 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction).
Proof: in degree `n`, a test étale `V/X` gives the terminal object `U_n ×_X V`
in the category of degree-`n` total objects over `V`. Thus the right Kan extension is
the limit of the component direct-image sheaves. Étale covers pull back to covers
in every degree, and limits of sheaves are sheaves. This includes the empty cover. -/
theorem totalEtaleAugmentationDirect_isSheaf {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf (totalEtaleTopology (U ⋙ Over.forget X)) (ModuleCat.{u + 1} Λ)) :
    Presheaf.IsSheaf X.smallEtaleTopology
      ((totalEtaleAugmentationDirectPresheaf U Λ).obj F) := by
  sorry

/-- Canonical direct image of the augmentation, with its actual compatible sections.
Source: Stacks Project, Tag 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction). -/
def totalEtaleAugmentationDirect {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    Sheaf (totalEtaleTopology (U ⋙ Over.forget X)) (ModuleCat.{u + 1} Λ) ⥤
      Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) where
  obj F := ⟨(totalEtaleAugmentationDirectPresheaf U Λ).obj F,
    totalEtaleAugmentationDirect_isSheaf U Λ F⟩
  map f := ⟨(totalEtaleAugmentationDirectPresheaf U Λ).map f⟩

/-- The compatible-section direct image has a left adjoint.
Source: Stacks Project, Tag 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction).
Proof: the inverse image sends a base sheaf to its inverse images on the components,
with the canonical composition transition maps. The component adjunctions identify
maps from this family to a total sheaf with maps to its compatible-section direct image.
These equivalences are natural and respect identities and composition, giving the
adjunction. Equivalently use left Kan extension and sheafification on the total site. -/
theorem totalEtaleAugmentationDirect_isRightAdjoint {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    (totalEtaleAugmentationDirect U Λ).IsRightAdjoint := by
  sorry

/-- Right adjoint structure from the named augmentation-adjunction theorem.
Source: Stacks Project, Tag 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction). -/
instance totalEtaleAugmentationDirect_rightAdjoint {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    (totalEtaleAugmentationDirect U Λ).IsRightAdjoint :=
  totalEtaleAugmentationDirect_isRightAdjoint U Λ

/-- Canonical inverse image, characterized by adjunction to the specified direct image.
Its component in degree `n` is inverse image along `U_n → X`, with the composition
transition maps. Source: Stacks Project, Tag 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction). -/
def totalEtaleAugmentationInverse {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ) ⥤
      Sheaf (totalEtaleTopology (U ⋙ Over.forget X)) (ModuleCat.{u + 1} Λ) :=
  (totalEtaleAugmentationDirect U Λ).leftAdjoint

/-- The ordinary augmentation adjunction; its unit fixes the derived normalization.
Source: Stacks Project, Tag 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction). -/
def totalEtaleAugmentationAdjunction {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    totalEtaleAugmentationInverse U Λ ⊣ totalEtaleAugmentationDirect U Λ :=
  Adjunction.ofIsRightAdjoint (totalEtaleAugmentationDirect U Λ)

/-- Exactness of augmentation inverse image.
Source: Stacks Project, Tag 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction).
Proof: inverse image is computed componentwise by the exact inverse images of the
small étale topoi, and finite limits of total sheaves are componentwise. Finite
colimits are preserved by its adjunction. Thus its additive inverse image is exact. -/
theorem totalEtaleAugmentationInverse_preservesFiniteLimits {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    PreservesFiniteLimits (totalEtaleAugmentationInverse U Λ) := by
  sorry

/-- Left exactness structure for the canonical inverse image.
Source: Stacks Project, Tag 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction). -/
instance totalEtaleAugmentationInverse_leftExact {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    PreservesFiniteLimits (totalEtaleAugmentationInverse U Λ) :=
  totalEtaleAugmentationInverse_preservesFiniteLimits U Λ

/-- The inverse image is a left adjoint for the specified ordinary adjunction.
Source: Stacks Project, Tag 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction). -/
instance totalEtaleAugmentationInverse_leftAdjoint {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    (totalEtaleAugmentationInverse U Λ).IsLeftAdjoint :=
  (totalEtaleAugmentationAdjunction U Λ).isLeftAdjoint

/-- Additivity of the inverse image follows from its left exactness.
Source: Stacks Project, Tag 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction). -/
instance totalEtaleAugmentationInverse_additive {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    (totalEtaleAugmentationInverse U Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Additivity of the direct image follows from its right adjunction.
Source: Stacks Project, Tag 0D70
(blueprint: def-trf-total-etale-augmentation-adjunction). -/
instance totalEtaleAugmentationDirect_additive {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] :
    (totalEtaleAugmentationDirect U Λ).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Component formula for the canonical augmentation inverse image.
Source: Stacks Project, Tag 0D70, proof of `lemma-augmentation-site`
(blueprint: def-trf-total-etale-augmentation-adjunction).
Proof: the family of component inverse images, with transition maps given by the
composition comparisons, is left adjoint to compatible sections. The universal property
of a left adjoint identifies it with `totalEtaleAugmentationInverse`. Evaluation in
any degree gives the displayed isomorphism, naturally in the base sheaf. -/
theorem totalEtaleAugmentationInverse_component {X : Scheme.{u}}
    (U : SimplicialObject (Over X)) (Λ : Type (u + 1)) [CommRing Λ] (n : ℕ) :
    Nonempty (totalEtaleAugmentationInverse U Λ ⋙
      totalEtaleRestriction (U ⋙ Over.forget X) n (ModuleCat.{u + 1} Λ) ≅
        Etale.upperStar (ModuleCat.{u + 1} Λ) (U.obj (op (SimplexCategory.mk n))).hom) := by
  sorry

end AlgebraicGeometry
