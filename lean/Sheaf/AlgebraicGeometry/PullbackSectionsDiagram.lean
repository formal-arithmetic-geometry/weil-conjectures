/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A3
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs

/-! # Canonical sections of inverse images along an inverse system -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Etale

/-- The adjunction units, corrected by direct- and inverse-image composition, form a
section diagram and a cocone on any tail of an inverse system. No affineness or
continuity assertion is needed for this coherence statement.

Source: Stacks Project, Etale Cohomology, Lemma 09YU (lemma-category-is-colimit),
proof, Fully faithful; the coherence argument is steps 2, 5 and 6 of the parent node.
(blueprint: lem-weil-pbc-pullback-sections-diagram)

Proof: Take the section module S_i at each stage and the displayed map mu_f on arrows.
The unit equation characterizing the inverse-image composition isomorphism identifies
mu_f with the unit for the composite morphism, transported through direct image.
Naturality of the unit and associativity of the direct-image composition then give
mu_g mu_f = mu_(fg). The identity composition comparison cancels the identity unit,
so mu_id = id. The same unit equation with the limit projection, and the cone equation,
gives tau_j mu_f = tau_i. Thus these objects and arrows define a functor F, the tau_i
define a cocone B, and the object comparisons e_i and eB can all be chosen as identities.
For module coefficients the units and composition maps are already module morphisms;
uniqueness of the adjoint comparison gives these same equations without forgetting the
module structure. This is only the coherence part, and asserts no colimit property. -/
theorem exists_pullbackSections_diagram {I : Type u} [Preorder I]
    (D : Iᵒᵖ ⥤ Scheme.{u}) (c : Cone D) (Λ : Type (u + 1)) [CommRing Λ] (i₀ : I)
    (G : Sheaf (D.obj (op i₀)).smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (V₀ : (D.obj (op i₀)).Etale) :
    let J := {i : I // i₀ ≤ i}
    let S : J → ModuleCat.{u + 1} Λ := fun i ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj
        ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)).obj.obj
          (op V₀)
    let T : ModuleCat.{u + 1} Λ := ((lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj
      ((upperStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).obj G)).obj.obj (op V₀)
    let μ : ∀ {i j : J}, (i ⟶ j) → (S i ⟶ S j) := fun {i j} f ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ)
          (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
          (D.map (homOfLE i.property).op) (D.map (homOfLE j.property).op)
          (by rw [← Functor.map_comp]; rfl)).hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE j.property).op)).map
          ((upperStarComp (ModuleCat.{u + 1} Λ)
            (D.map (homOfLE (show i.val ≤ j.val from leOfHom f)).op)
            (D.map (homOfLE i.property).op) (D.map (homOfLE j.property).op)
            (by rw [← Functor.map_comp]; rfl)).inv.app G)).hom.app (op V₀)
    let τ : ∀ i : J, S i ⟶ T := fun i ↦
      ((lowerStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))).unit.app
            ((upperStar (ModuleCat.{u + 1} Λ) (D.map (homOfLE i.property).op)).obj G)) ≫
        (lowerStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))
          (D.map (homOfLE i.property).op) (c.π.app (op i₀))
          (c.w (homOfLE i.property).op).symm).hom.app _ ≫
        (lowerStar (ModuleCat.{u + 1} Λ) (c.π.app (op i₀))).map
          ((upperStarComp (ModuleCat.{u + 1} Λ) (c.π.app (op i.val))
            (D.map (homOfLE i.property).op) (c.π.app (op i₀))
            (c.w (homOfLE i.property).op).symm).inv.app G)).hom.app (op V₀)
    ∃ (F : J ⥤ ModuleCat.{u + 1} Λ) (B : Cocone F)
      (e : ∀ i : J, F.obj i ≅ S i) (eB : B.pt ≅ T),
      (∀ (i j : J) (f : i ⟶ j), (e i).inv ≫ F.map f ≫ (e j).hom = μ f) ∧
      (∀ i : J, (e i).inv ≫ B.ι.app i ≫ eB.hom = τ i) := by
  sorry

end AlgebraicGeometry.Etale
