/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group X2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.Small.Basic
public import Mathlib.AlgebraicGeometry.AffineScheme
import Sheaf.AlgebraicGeometry.PerfectAffineBoundedProjective

/-! # Smallness of perfect isomorphism classes on an affine scheme

Source: Step 1 of lem-pc-perfect-complexes-compact-set, using Stacks Project,
Tag 08EB (blueprint: lem-pc-perfect-affine-classes-small).
-/

@[expose] public section

universe u w

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- Perfect quasi-coherent derived objects on an affine scheme have `u`-small
isomorphism classes.
Source: Step 1 of lem-pc-perfect-complexes-compact-set; Stacks Project, Tag 08EB
(blueprint: lem-pc-perfect-affine-classes-small).

Proof: Identify `Y` with `Spec Γ(Y, 𝒪_Y)` using `Y.isoSpec`, and transport the
module categories, their derived categories, quasi-coherence and perfectness along
this isomorphism. Apply `perfect_iff_affine_bounded_projective`. In each degree,
a finite projective module is a direct summand of a finite free module `A^n` and
is isomorphic to the image of an idempotent endomorphism of `A^n`. Encode its
image as a submodule of `A^n`. Alternatively use Mathlib's small model of
`FGModuleCat A` (`Mathlib.Algebra.Category.FGModuleCat.EssentiallySmall`),
restricting its terms to projective ones. The natural numbers, integer degree bounds,
submodules of finite free modules, and linear maps between such submodules are
all `u`-small. The differential identities and boundedness are predicates on
these data, so the type of encoded complexes is `u`-small. Transport each bounded
finite projective complex termwise to such an encoded complex, conjugating the
differentials by the chosen module isomorphisms. The resulting complex isomorphism
induces an isomorphism of associated derived sheaves. Restrict the encoded models
to those yielding perfect quasi-coherent objects. Their map to the skeleton of
the full subcategory is surjective, and `small_of_surjective` gives the result.
The zero ring and zero complex are included; no nonempty index or nonzero term
is required. -/
theorem small_perfectComplex_classes_of_isAffine (Y : Scheme.{u}) [IsAffine Y]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ V : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over V))] :
    Small.{u} (Skeleton (ObjectProperty.FullSubcategory
      (fun E : schemeDerivedQCohCategory Y ↦ IsPerfect Y E.obj))) := by sorry

end AlgebraicGeometry.Scheme
