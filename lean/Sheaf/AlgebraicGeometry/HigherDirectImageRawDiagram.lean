/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.HigherDirectImageRawOverNaturality

/-! # The raw cohomology diagram

Source: Stacks Project, Tag 09Z1, the canonical cohomology comparison maps.
(blueprint: lem-sbc-higher-image-raw-pullback-functorial).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The explicit raw pullbacks satisfy identity and composition, independently of any
limit, affineness, or quasi-compactness assumption.
Source: Stacks Project, Tag 09Z1, canonical comparison maps in lemma-relative-colimit.
(blueprint: lem-sbc-higher-image-raw-pullback-functorial).

Proof: The derived inverse-image functor is additive, and composition with fixed
morphisms is additive in each argument. Thus the five-factor formula preserves zero
and addition. Expand the five factors defining raw pullback. For an identity morphism, the
identity comparison for inverse image cancels the single-functor comparison and its
inverse. Naturality of the shift comparison cancels its identity factors, leaving the
original derived morphism. For composable arrows, functoriality of derived inverse image
moves the five factors of the first pullback through those of the second. Naturality of
the single-functor comparison cancels the adjacent inverse and direct comparisons.
The associativity coherence of inverse-image composition identifies the resulting
source comparison with that for the composite. Its coefficient comparison is identified
in the same way, using the two equations defining morphisms in Over W. Compatibility of
derived inverse image with shifts identifies the remaining shift comparison. Thus the
five surviving factors are exactly those of the composite raw pullback. -/
theorem higherDirectImageRawOverPullback_functorial
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale) :
    (∀ (A B : Over W) (f : A ⟶ B),
      higherDirectImageRawOverPullback Λ k G q f U 0 = 0) ∧
    (∀ (A B : Over W) (f : A ⟶ B)
      (x y : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)),
      higherDirectImageRawOverPullback Λ k G q f U (x + y) =
        higherDirectImageRawOverPullback Λ k G q f U x +
          higherDirectImageRawOverPullback Λ k G q f U y) ∧
    (∀ (A : Over W)
      (z : (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U)),
      higherDirectImageRawOverPullback Λ k G q (𝟙 A) U z = z) ∧
    (∀ (A B C : Over W) (f : A ⟶ B) (g : B ⟶ C)
      (z : (higherDirectImageRawOverPresheaf Λ k G q C).obj (op U)),
      higherDirectImageRawOverPullback Λ k G q (f ≫ g) U z =
        higherDirectImageRawOverPullback Λ k G q f U
          (higherDirectImageRawOverPullback Λ k G q g U z)) := by
  sorry

/-- The additive map on raw cohomology; its data are the explicit five-factor formula. -/
noncomputable def higherDirectImageRawOverPullbackHom
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale) :
    (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U) ⟶
      (higherDirectImageRawOverPresheaf Λ k G q A).obj (op U) :=
  ConcreteCategory.ofHom (C := AddCommGrpCat)
    { toFun := higherDirectImageRawOverPullback Λ k G q f U
      map_zero' := (higherDirectImageRawOverPullback_functorial Λ k G q U).1 A B f
      map_add' := (higherDirectImageRawOverPullback_functorial Λ k G q U).2.1 A B f }

/-- The bundled additive map is exactly the prescribed raw pullback. -/
theorem higherDirectImageRawOverPullbackHom_apply
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {A B : Over W} (f : A ⟶ B) (U : S.Etale)
    (z : (higherDirectImageRawOverPresheaf Λ k G q B).obj (op U)) :
    higherDirectImageRawOverPullbackHom Λ k G q f U z =
      higherDirectImageRawOverPullback Λ k G q f U z := rfl

/-- The contravariant raw cohomology functor on Over W. No data are chosen from an
existence theorem: objects and maps are the fixed raw presheaves and explicit pullbacks. -/
noncomputable def higherDirectImageRawOverFunctor
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ) (U : S.Etale) :
    (Over W)ᵒᵖ ⥤ AddCommGrpCat.{u + 1} where
  obj A := (higherDirectImageRawOverPresheaf Λ k G q A.unop).obj (op U)
  map f := higherDirectImageRawOverPullbackHom Λ k G q f.unop U
  map_id A := by
    apply AddCommGrpCat.ext
    intro z
    change higherDirectImageRawOverPullbackHom Λ k G q (𝟙 A.unop) U z = z
    rw [higherDirectImageRawOverPullbackHom_apply]
    exact (higherDirectImageRawOverPullback_functorial Λ k G q U).2.2.1 A.unop z
  map_comp f g := by
    apply AddCommGrpCat.ext
    intro z
    change higherDirectImageRawOverPullbackHom Λ k G q (g.unop ≫ f.unop) U z =
      higherDirectImageRawOverPullbackHom Λ k G q g.unop U
        (higherDirectImageRawOverPullbackHom Λ k G q f.unop U z)
    simp only [higherDirectImageRawOverPullbackHom_apply]
    exact (higherDirectImageRawOverPullback_functorial Λ k G q U).2.2.2
      _ _ _ g.unop f.unop z

/-- The raw cohomology diagram of an inverse system. -/
noncomputable abbrev higherDirectImageRawDiagram
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (U : S.Etale) :=
  D.op ⋙ higherDirectImageRawOverFunctor Λ k G q U

/-- The raw cohomology cocone of a scheme cone, before any assertion of continuity. -/
noncomputable def higherDirectImageRawCocone
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℤ)
    {I : Type u} [Category.{u} I] (D : I ⥤ Over W) (c : Cone D) (U : S.Etale) :
    Cocone (higherDirectImageRawDiagram Λ k G q D U) :=
  (higherDirectImageRawOverFunctor Λ k G q U).mapCocone c.op

end AlgebraicGeometry.Etale
