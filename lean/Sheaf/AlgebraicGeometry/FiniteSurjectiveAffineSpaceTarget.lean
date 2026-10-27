/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group N0
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus
import Sheaf.AlgebraicGeometry.AlgebraicSpaceUCSurjectionSeparation
import Sheaf.AlgebraicGeometry.SpaceChangeBase
import Sheaf.AlgebraicGeometry.FiniteSpaceFinitePresentationLimit
import Sheaf.AlgebraicGeometry.SpaceFpOverSpaceLimitDescent
import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperFpLocality
import Sheaf.AlgebraicGeometry.SpaceEventuallyFiniteMap
import Sheaf.AlgebraicGeometry.AlgebraicSpaceEventuallySurjectiveMap

/-!
# Affine targets of finite surjective maps of algebraic spaces

Source: Stacks Project, Limits of Spaces, Tag 07VS (lemma-affine);
Properties of Spaces, Tag 03H5 (blueprint: lem-sfb-finite-surjective-affine-space-target).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.AlgebraicSpace

/-- The target of a finite surjective map from an affine algebraic space is affine.
Surjectivity is expressed by the image on field-valued point classes being the whole set.
Affineness means representability over the given base by an affine scheme.
Source: Stacks Project, Limits of Spaces, Tag 07VS; Properties of Spaces, Tag 03H5
(blueprint: lem-sfb-finite-surjective-affine-space-target).

Proof:
1. Finiteness on scheme tests implies properness by lem-weil-pbc-finite-proper and
   lem-sfb-space-representable-proper-tests, hence universal closedness. The affine source
   is qcqs by lem-weil-pbc-affine-scheme-qcqs. Its continuous point surjection makes the
   target quasi-compact (lem-a1-space-point-open-calculus); the target is quasi-separated
   by lem-sfb-space-uc-surjection-separation. Change base to Spec Z using
   lem-sfb-space-change-base-to-integers, preserving the atlas, tests and point classes.
2. Apply lem-sfb-space-finite-fp-approximation to express X as a limit of finite finitely
   presented spaces over Y, with affine transitions. The stages are qcqs by
   lem-sfb-space-fp-qcqs-source. By lem-sfb-space-affine-limits-schematic-stages some stage
   is affine; its map to Y is surjective because the original map factors through it.
   Replace X by that stage to arrange that f is finitely presented as well.
3. Use lem-sfb-space-absolute-noetherian-approximation to write Y as a directed limit of
   Noetherian qcqs spaces with affine transitions. By
   lem-sfb-space-fp-over-space-limit-descent, descend f to a finitely presented map at one
   stage and form its base changes over the directed tail. These sources are qcqs by
   lem-sfb-space-flat-proper-fp-locality and lem-sfb-space-fp-qcqs-source; transitions are
   affine by lem-sfb-space-affine-locality, and their limit is X by
   lem-sfb-space-affine-limits-schematic-stages.
4. Finite presentation implies local finite type. Apply lem-sfb-space-eventually-finite-map
   and lem-sfb-space-eventually-surjective-map to make the stage maps finite surjective.
   By lem-sfb-space-affine-limits-schematic-stages the sources are eventually affine.
   Choose a common upper bound. The target stage is then affine by
   lem-sfb-noetherian-space-finite-affine-descent.
5. The limit projection to that affine stage is affine by
   lem-sfb-space-affine-limits-schematic-stages, so Y is affine by
   lem-sfb-space-affine-locality. The equivalence in lem-sfb-space-change-base-to-integers
   equips its affine representing scheme with the original map to S. -/
theorem exists_affine_representation_of_finite_surjective {S : Scheme.{u}}
    {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (hX : ∃ U : Over S, IsAffine U.left ∧ Nonempty (X.obj.obj ≅ yoneda.obj U))
    (hfinite : IsRepresentableWith (fun _ _ p ↦ IsFinite p.left) f.hom.hom)
    (hsurj : pointImage f.hom.hom = Set.univ) :
    ∃ V : Over S, IsAffine V.left ∧ Nonempty (Y.obj.obj ≅ yoneda.obj V) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
