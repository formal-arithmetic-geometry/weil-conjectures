/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B2
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FinitenessCoefficient
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar

import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Sheaf.AlgebraicGeometry.BoundedConstructibleDevissage
import Sheaf.AlgebraicGeometry.BoundedConstructibleLowerStarSingleUpperBound

/-! # BoundedConstructibleLowerStarPreservation

Finite truncation induction reduces boundedness of direct image to the single-sheaf bound.
-/

@[expose] public section

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

universe u

open scoped CategoryTheory.Obj
open CategoryTheory Limits MonoidalCategory Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) [MonObj Λ]
  [IsCommMonObj Λ] (ℓ : ℕ) [Fact ℓ.Prime] {k : Type u} [Field k]
  [Fact (ringChar k).Prime] [Fact (ringChar k ≠ ℓ)]
variable {X Y : Over (Spec (.of k))}
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  (f : X ⟶ Y)

/-- The direct image of a bounded constructible complex is bounded once upper bounds
are known for direct images of constructible sheaves placed in degree zero.

Source: blueprint `lem-sfb-dc-lower-star-preserves`, finite cohomological devissage.
The inverse image of the bounded subcategory under the triangulated right derived functor
is triangulated and closed under isomorphisms. A constructible sheaf in degree zero has
bounded direct image: left t-exactness gives lower bound zero, and single-sheaf finiteness
gives an upper bound. Finite truncation induction now puts every bounded constructible
input in this inverse image.
(blueprint: lem-sfb-dc-lower-star-bounded) -/
theorem boundedConstructible_rightDerivedLowerStar_bounded
    [IsFinitenessCoefficient ℓ Λ]
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X.left) Ab.{u + 1})
      (condensedRingObj Λ X.left)))
    (hK : boundedConstructible (condensedRingObj Λ X.left) K) :
    (DerivedCategory.TStructure.t.bounded
      : ObjectProperty (DerivedCategory (Mod
        (Sheaf (Scheme.ProEt.topology Y.left) Ab.{u + 1})
        (condensedRingObj Λ Y.left)))) ((R((f.left)_*⟦Λ⟧)).obj K) := by
  apply prop_of_boundedConstructibleModule
    (DerivedCategory.TStructure.t.bounded.inverseImage (R((f.left)_*⟦Λ⟧))) ?_ hK
  intro F hF
  have hge : ((R((f.left)_*⟦Λ⟧)).obj
      ((DerivedCategory.singleFunctor _ 0).obj F)).IsGE 0 := by
    let K' : DerivedCategory.Plus _ :=
      ⟨(DerivedCategory.singleFunctor _ 0).obj F, ⟨0, inferInstance⟩⟩
    have h0 : ((DerivedCategory.singleFunctor _ 0).obj F).IsGE 0 := inferInstance
    have : K'.IsGE 0 := (K'.isGE_ι_obj_iff 0).1 h0
    refine (DerivedCategory.isGE_iff _ 0).2 fun q hq ↦ ?_
    exact ((lowerStar Λ f.left).isZero_homologyFunctor_rightDerivedFunctorPlus_obj_of_isGE
      K' 0 hq).of_iso
      ((DerivedCategory.homologyFunctor _ q).mapIso
        ((lowerStar Λ f.left).rightDerivedFunctorPlusCompatibility.app K')).symm
  refine ⟨⟨0, hge⟩, ?_⟩
  exact constructible_single_rightDerivedLowerStar_upper_bounded Λ ℓ f F hF

end AlgebraicGeometry.ProEtale.CondensedRing
