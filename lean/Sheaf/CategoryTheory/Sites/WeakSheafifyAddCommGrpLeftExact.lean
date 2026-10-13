/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import Mathlib.Algebra.Category.Grp.Basic
public import Mathlib.CategoryTheory.Sites.LocallyBijective

/-! # Left exactness of existing abelian sheafification

Source: Stacks Project, Tag 00WJ and Tag 03CN.
(blueprint: lem-sc-weak-sheafify-addcommgrp-left-exact). -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

/-- An existing abelian sheafification whose inverted maps are exactly the locally
bijective maps is left exact, independently of the size of the site.

Source: Stacks Project, Tag 00WJ (left exactness of sheafification), applied to
abelian presheaves as in Tag 03CN, proof of the first assertion.
(blueprint: lem-sc-weak-sheafify-addcommgrp-left-exact)

Proof: finite limits of abelian presheaves are computed sectionwise. For a finite
category K and a diagram D, form the map from the limit of D to the limit of the
sheafified diagram, using the units of sheafification. This map is locally
bijective. For local surjectivity, lift the finitely many components of a section
on a common covering, and then refine that covering so that the finitely many
compatibility equations hold, using local injectivity of the units. For local
injectivity, refine the finitely many coverings on which two components agree.
The empty diagram gives the terminal presheaf, which is already a sheaf. Limits
of sheaves are computed as limits of their underlying presheaves, so the target
of this comparison is a sheaf. By the assumed characterization of inverted
maps, sheafifying the comparison is an isomorphism. The counit on its sheaf
target is also an isomorphism; hence the canonical finite-limit comparison of
the given left adjoint is an isomorphism. This proves preservation of every
finite limit. Together with the given right-adjoint instance for the inclusion,
this is exactly HasSheafify. No construction of larger-universe sheafification
or smallness of the site is used. -/
theorem hasSheafify_addCommGrp_of_weak
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasWeakSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}] :
    HasSheafify J AddCommGrpCat.{w} := by sorry

end CategoryTheory
