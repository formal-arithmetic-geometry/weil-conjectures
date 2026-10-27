/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M4
-/
module

public import Sheaf.Paper.ComponentLiftSectionDefs

/-! # Evaluation and functoriality of component-lift sections

Source: Hemo--Richarz--Scholbach, Definition 3.3, Lemma 4.1 and Proposition 4.3(3).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

/-- Evaluation at one identifies the actual normalized derived Hom pullback with the
module section map and records the functorial laws of that section map.

Source: HRS (4.2); Stacks 08JJ, global Hom at the coefficient unit
(blueprint: lem-sfb-component-lift-section-normalization).

Proof: the fully faithful singleFunctor identifies derived Hom between single complexes
with ordinary module Hom. A map from the regular module is determined by its value at
one on the terminal test: at W it sends r to r times the restriction of this value.
Conversely this formula defines a module map, by associativity of the action and
naturality of restrictions; the two constructions are inverse. This proves the asserted
bijection for every module, without any lisse or affineness hypothesis.
Naturality of the module adjunction unit with respect to this map, together with the
mate equation for the coefficient map, identifies evaluation of the normalized pullback
with the adjunction-unit section followed by terminal restriction. The single-functor
comparison of the exact derived pullback gives precisely ComponentLiftSectionIdentity.
Naturality in a module morphism is the naturality square for that adjunction unit,
followed by the restriction square of the underlying sheaf morphism. The unit of the
composite adjunction is the first unit followed by pushforward of the second; the
canonical upperStarComp is its adjunction mate. Evaluating this equality at the terminal
test gives ComponentLiftSectionComposition. The identity adjunction gives the final
identity equation under upperStarId. Empty schemes and zero modules satisfy the same
formulas. -/
theorem component_lift_section_normalization
    (Λ : Profinite.CondensedRing.{u}) [IsCommMonObj Λ.X] :
    (∀ (U V : Scheme.{u}) (g : V ⟶ U),
      ComponentLiftSectionIdentity Λ g ∧ ComponentLiftSectionNaturality Λ g) ∧
    (∀ (T : Scheme.{u})
      (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T)),
      Function.Bijective (componentLiftHomSection Λ T L)) ∧
    (∀ (T : Scheme.{u})
      (L : Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1}) (condensedRingObj Λ.X T))
      (s : (condensedModuleSections Λ.X T).obj L),
      (condensedModuleSections Λ.X T).map ((upperStarId Λ.X T).hom.app L)
        ((componentLiftSectionPullback Λ (𝟙 T) L) s) = s) ∧
    (∀ (U V W : Scheme.{u}) (g : V ⟶ U) (h : W ⟶ V),
      ComponentLiftSectionComposition Λ g h) := by sorry

end AlgebraicGeometry.ProEtale.CondensedRing
