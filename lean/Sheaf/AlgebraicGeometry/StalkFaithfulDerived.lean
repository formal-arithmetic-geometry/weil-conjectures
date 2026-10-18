/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NC
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategories
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.CategoryTheory.Sites.Point.Skyscraper
import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Sheaf.AlgebraicGeometry.EtaleInverseImageExact
import Sheaf.AlgebraicGeometry.GeometricStalkAsPullback
import Sheaf.AlgebraicGeometry.GeometricStalkCohomology
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm
import Sheaf.AlgebraicGeometry.DerivedGlobalGerm
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact

/-!
# Stalk faithfulness for derived étale objects

Source: literature/blueprint/master/blueprint/sec-smooth-purity/
`sk-prop-sf-kunneth-ordinary/lem-kun-stalk-faithful-derived.md`
(blueprint: lem-kun-stalk-faithful-derived).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open AlgebraicGeometry

namespace AlgebraicGeometry.Etale

/-- A morphism in the unbounded derived category of abelian étale sheaves is an isomorphism
if and only if its derived inverse image at every geometric point is an isomorphism.
Source: blueprint `sec-smooth-purity/sk-prop-sf-kunneth-ordinary/lem-kun-stalk-faithful-derived.md`,
node order 1703 (blueprint: lem-kun-stalk-faithful-derived).

Proof:
1. Complete α to a distinguished triangle K → L → C → K[1] in the derived category
   (def-weil-pbc-derived-categories, def-weil-triangulated-category). By
   lem-kun-distinguished-cone-zero, α is invertible exactly when C is zero.
2. Geometric inverse image is exact and additive (prop-weil-pbc-inverse-image-exact),
   so it induces a triangulated functor on unbounded derived categories
   (lem-sf-exact-functor-derived-triangulated). On a representing complex the cone is
   C(f)^q = B^q ⊕ A^(q+1), with differential matrix (d_B, f; 0, -d_A)
   (def-weil-abstract-derived-category). Additivity and preservation of finite sums
   preserve this matrix, inclusion and negative projection. Thus the image triangle
   has cone C_t and first map the pulled-back α. By lem-kun-stalk-as-pullback this is
   the derived geometric pullback.
3. For every integer q, lem-kun-stalks-of-cohomology identifies the stalk of H^q(C)
   with H^q(C_t), viewed as a group via the equivalence of point sheaves and groups
   (lem-weil-pbc-geometric-point-pullback-stalk). The equivalence reflects zero objects.
4. Apply lemma-weil-pbc-geometric-stalk-conservative to 0 → H^q(C). Exactness of
   geometric stalks (prop-weil-pbc-geometric-stalks-exact) sends the zero sheaf to zero.
   Hence H^q(C) vanishes precisely when all its geometric stalks vanish.
5. By lem-kun-d-zero-cohomology, C vanishes precisely when every H^q(C) vanishes.
   Steps 3 and 4 and interchange of the universal quantifiers identify this with
   vanishing of every cohomology sheaf of every C_t. Apply the same cohomology criterion
   on Spec Ω, and then lem-kun-distinguished-cone-zero to the image triangle. This is
   equivalent to invertibility of every pulled-back α, giving both directions without
   any boundedness assumption. -/
theorem stalk_faithful_derived
    {T : Scheme.{u}}
    {K L : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})}
    (α : K ⟶ L) :
    IsIso α ↔
      ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ T),
        IsIso ((upperStar AddCommGrpCat.{u + 1} t).mapDerivedCategory.map α) := by
  sorry

end AlgebraicGeometry.Etale
