/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
import WeilConjectures.CategoryTheory.Monoidal.Mod.Limits

/-!
# Finite exactness of restriction between internal module categories

Source: blueprint `main-20261015`, `sec-six-functors-basics`,
`sk-def-sfb-module-lower-shriek/def-sfb-module-open-lower-shriek.proof.md`, first sentence;
internal-module constructions in `WeilConjectures.CategoryTheory.Monoidal.Mod.Limits`
(blueprint: lem-sfb-modobj-restriction-finite-exact).
-/

@[expose] public section

universe v u

open CategoryTheory.Limits CategoryTheory.MonoidalCategory

namespace CategoryTheory.Mod

/-- Source: blueprint `main-20261015`, `sec-six-functors-basics`, proof of
`def-sfb-module-open-lower-shriek`, first sentence
(blueprint: lem-sfb-modobj-restriction-finite-exact).

If tensoring on the left with either monoid preserves finite colimits, both internal module
categories have finite limits and colimits, and restriction of scalars is exact. Here
`exactFunctor` means precisely preservation of finite limits and finite colimits. No braiding,
closedness, additivity, commutativity, or invertibility of the monoid morphism is required.

Proof plan:
1. For either monoid and every finite diagram, lift its underlying limit and colimit using
   `lem-sfb-modobj-forget-creates` (the constructions `Mod.createsLimit` and
   `Mod.createsColimit`). The colimit construction applies by the finite-colimit preservation
   hypothesis for that monoid. This gives all four existence assertions.
2. The definition `Mod.comap` (`def-sfb-modobj-restriction`) retains underlying objects,
   morphisms, cones, and cocones, replacing an action by its composite with the monoid map.
3. A lifted underlying limit cone remains limiting after restriction: uniqueness of the
   lifted action identifies the restricted action with the limit action for the other monoid.
   For any other limiting cone, the unique mutually inverse cone maps to the chosen lifted
   cone remain mutually inverse after applying restriction, so its image is limiting too.
4. Likewise, a lifted underlying colimit cocone remains colimiting: both left tensor functors
   preserve the finite colimit, so uniqueness of the lifted action identifies the restricted
   action with the colimit action for the other monoid. The mutually inverse comparison
   cocone maps transfer this property to the image of every colimiting cocone.
5. These two preservation properties give `exactFunctor`, as defined in
   `def-galois-exact-functor`; the four existence assertions give its intended setting.
-/
theorem finite_limits_colimits_exact_comap
    {C : Type u} [Category.{v} C] [MonoidalCategory C]
    [HasFiniteLimits C] [HasFiniteColimits C]
    {R S : C} [MonObj R] [MonObj S] (φ : R ⟶ S) [IsMonHom φ]
    [PreservesFiniteColimits (tensorLeft R)] [PreservesFiniteColimits (tensorLeft S)] :
    HasFiniteLimits (Mod C R) ∧ HasFiniteColimits (Mod C R) ∧
      HasFiniteLimits (Mod C S) ∧ HasFiniteColimits (Mod C S) ∧
      exactFunctor (Mod C S) (Mod C R) (comap (D := C) φ) := by
  have hRlim : HasFiniteLimits (Mod C R) := ⟨fun _ _ _ ↦ inferInstance⟩
  have hRcolim : HasFiniteColimits (Mod C R) := ⟨fun _ _ _ ↦ inferInstance⟩
  have hSlim : HasFiniteLimits (Mod C S) := ⟨fun _ _ _ ↦ inferInstance⟩
  have hScolim : HasFiniteColimits (Mod C S) := ⟨fun _ _ _ ↦ inferInstance⟩
  refine ⟨hRlim, hRcolim, hSlim, hScolim, ?_⟩
  rw [exactFunctor_iff]
  constructor
  · refine ⟨fun J _ _ ↦ ?_⟩
    have : PreservesLimitsOfShape J (comap (D := C) φ ⋙ forget R) :=
      inferInstanceAs (PreservesLimitsOfShape J (forget (D := C) S))
    exact preservesLimitsOfShape_of_reflects_of_preserves (comap φ) (forget R)
  · refine ⟨fun J _ _ ↦ ?_⟩
    have : PreservesColimitsOfShape J (comap (D := C) φ ⋙ forget R) :=
      inferInstanceAs (PreservesColimitsOfShape J (forget (D := C) S))
    exact preservesColimitsOfShape_of_reflects_of_preserves (comap φ) (forget R)

end CategoryTheory.Mod
