/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R2
-/
module

public import Sheaf.AlgebraicGeometry.FlatBaseChangeMapSectionsDefs
import Sheaf.AlgebraicGeometry.ModuleOpenRestrictionInjectives

/-! # FlatBaseChangeOpenChoicesExist

Source: Stacks Project, Cohomology, Tags 02N7, 01FB and 01E4.
-/

@[expose] public section
universe uBC
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules
attribute [local instance] AlgebraicGeometry.Scheme.Modules.enoughInjectives

/-- Compatible restricted resolutions and the restricted adjunction unit exist.
Source: Stacks, Cohomology, Tags 01E1, 01FB, 01E4; Modules, Tag 01AJ.
(blueprint: lem-weil-pbc-flat-base-change-open-choices-exist).

Proof: Restrict I and J termwise to U = f⁻¹V and W = g'⁻¹U. Restriction is exact
 and preserves injectives: transport the overFunctor results across
 overFunctorEquiv, as in module_sections_acyclic_of_cohomology_vanishing. Thus
 the restricted augmentations give resolutions of the restricted modules.
 Identify sections using restrictAppIso, evaluated at
 the top open, followed by the equality that the inclusion maps the top to U
 (respectively W). These identifications satisfy the specified components.
 Restrict the original pullback unit to U and transpose across restriction's
 adjunction to define psi. On an open T in U, the unit sends m to 1 tensor m;
 restricting the original unit gives the same map on h⁻¹T. With the canonical
 pushforward composition identifications this is exactly unit_square. Bundle
 these choices to obtain the required inhabitant. -/
theorem flatBaseChangeMap_sections_choices {X S S' : Scheme.{uBC}} (f : X ⟶ S) (g : S' ⟶ S)
    [Flat g] [Flat (pullback.snd g f)] (F : X.Modules) :
    ∀ (I : InjectiveResolution F)
      (J : InjectiveResolution ((tensorPullback (pullback.snd g f)).obj F)) (V : S.Opens),
      Nonempty (FlatBaseChangeOpenChoices f g F I J V) := by
  sorry


end AlgebraicGeometry.Scheme.Modules
