/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q151
-/
module

public import Sheaf.AlgebraicGeometry.SpaceGeometricSetStalk
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.CategoryTheory.Sites.Limits

import Sheaf.AlgebraicGeometry.ChartwiseEtalePermanence
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import Mathlib.CategoryTheory.Limits.Types.Filtered
import Mathlib.CategoryTheory.Limits.FilteredColimitCommutesFiniteLimit
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Sites.LocallySurjective

/-! # Geometric set stalks of algebraic spaces

Source: Stacks Project, Properties of Spaces, Tags 04JY, 04K0, 04K1 and 04K5
(blueprint: lem-sfb-space-etale-conservative-geometric-points).
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.AlgebraicSpace

variable {S : Scheme.{u}}

/-- Geometric stalks preserve finite limits and all small colimits, and jointly detect
monomorphisms, epimorphisms, isomorphisms, and equality of maps, including the empty space.
Source: Stacks 04K0, 04K1, 04K5
(blueprint: lem-sfb-space-etale-conservative-geometric-points).

Proof: pointed étale neighbourhoods are cofiltered, by pointed fibre products and
étale equalizers. Finite limits of sheaves are sectionwise, and filtered colimits of
sets commute with finite limits. For a set A the sheaf U ↦ Map(Hom_X(Spec Ω,U),A)
is right adjoint to the displayed stalk: a map out of the colimit sends a section s
and lift l to its germ [U,l,s]. Covering lifts over an algebraically closed field
prove its sheaf condition. The adjunction proves preservation of all colimits.
A section or a pair of sections can be tested on geometric lifts of all points of
its chart. Equality of germs gives an étale covering on which the sections agree;
local lifting gives an étale covering on which a requested preimage exists. Thus
injectivity and surjectivity on stalks detect monos and epis. A mono and epi of
sheaves of sets is an iso. Apply the same local equality argument to two maps.
On the empty space the empty covering forces every section set to be a singleton,
so all assertions, including the vacuous point tests, remain valid. -/
theorem etaleSetStalk_conservative (X : AlgebraicSpace S) :
    (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
      (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj),
      PreservesFiniteLimits (etaleSetStalk.{u, w} x) ∧
        PreservesColimitsOfSize.{max (u + 1) w, max (u + 1) w}
          (etaleSetStalk.{u, w} x)) ∧
    (∀ (F G : Sheaf X.etaleTopology (Type (max (u + 1) w))) (a : F ⟶ G),
      (Mono a ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj),
          Function.Injective ((etaleSetStalk x).map a)) ∧
      (Epi a ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj),
          Function.Surjective ((etaleSetStalk x).map a)) ∧
      (IsIso a ↔ ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (s : Spec (.of Ω) ⟶ S) (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj),
          Function.Bijective ((etaleSetStalk x).map a))) ∧
    (∀ (F G : Sheaf X.etaleTopology (Type (max (u + 1) w))) (a b : F ⟶ G),
      (∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ S)
        (x : yoneda.obj (Over.mk s) ⟶ X.obj.obj),
        (etaleSetStalk x).map a = (etaleSetStalk x).map b) → a = b) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
