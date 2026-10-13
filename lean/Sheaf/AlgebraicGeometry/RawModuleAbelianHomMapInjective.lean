/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W3
-/
module

public import Sheaf.AlgebraicGeometry.RawModuleAbelianHomMap

/-! # Injective raw scalar comparison

Source: Stacks Project, Tag 03FD, injective-resolution comparison.
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- Injective of the raw scalar comparison on underlying groups.
Source: Stacks Project, Tag 03FD, lemma-cohomology-modules-abelian-agree.
(blueprint: lem-sbc-raw-module-abelian-hom-map-injective).

Proof: Let two module derived classes have the same image and subtract them.
Resolve A.hom^*G by injective module sheaves and represent the difference by a
cocycle in sections over V = U times_S A.left. Free represented sheaves
corepresent sections after pullback. Forgetting scalars leaves the section
complex unchanged, and Tag 03FD says its terms are acyclic for abelian sections.
Thus its cohomology also computes the target abelian derived Hom group. The
explicit scalar map carries the chosen cocycle to the identical section cocycle:
freeMap sends the identity generator to itself, and the pullback, single and
shift comparisons are the canonical adjunction identifications. Its image being
zero means this section cocycle is a boundary in that same complex. The identical
boundary is a boundary in the module section complex, so the original difference
class is zero. Additivity now proves equality of the two original classes.
The argument applies to degree zero (where boundaries in degree -1 are zero),
the zero ring and empty V. -/
theorem rawModuleAbelianHomMap_injective
    (Λ : Type (u + 1)) [CommRing Λ] {W S : Scheme.{u}} (k : W ⟶ S)
    (G : Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (q : ℕ)
    (U : S.Etale) (A : Over W) :
    Function.Injective (rawModuleAbelianHomMap Λ k G q U A).hom := by sorry

end AlgebraicGeometry.Etale
