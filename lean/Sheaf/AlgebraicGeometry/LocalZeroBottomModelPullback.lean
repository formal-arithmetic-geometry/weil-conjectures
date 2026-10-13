/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group W2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
import Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback
import Sheaf.AlgebraicGeometry.DerivedPullbackComposition
import Sheaf.AlgebraicGeometry.DerivedOpenPullbackHomology
import Sheaf.AlgebraicGeometry.PerfectAffineMapRepresentative

/-! # Bottom cohomology of local zero-differential models
Source: Stacks Project, Tag 0BDL, pullback clause; Tags 06YD and 06YJ.
(blueprint: lem-sc-local-zero-bottom-model-pullback). -/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
set_option autoImplicit false
namespace AlgebraicGeometry.Scheme

/-- A locally bounded finite-free model with zero bottom differential has bottom
cohomology compatible with every derived pullback.
Source: Stacks Project, Tag 0BDL, pullback comparison clause; Tags 06YD, 06YJ and 0D5S.
(blueprint: lem-sc-local-zero-bottom-model-pullback).

Proof:
1. On a neighbourhood U furnished by hmodel, the complex K is bounded above
   and finite free, hence K-flat. Both differentials adjacent to degree a vanish:
   the incoming one has zero source and the outgoing one is zero by hypothesis.
   Consequently H^a(K) is canonically K^a, with the identification given by the
   kernel of zero and cokernel of zero, not by a choice of basis.
2. Restrict g to the inverse image of U. The flat-complex counit represents Lg*D
   by the termwise tensor pullback of K. This complex also has zero terms below a
   and zero outgoing differential at a. Its H^a is canonically g*K^a. Exact open
   restriction identifies these computations with restrictions of the two global
   homology sheaves. Thus the bottom comparison is an isomorphism on this open.
3. Refine overlaps by affine opens W. Restrict both models to W and transport
   between modules on W and modules on its localized open site. They are strictly
   perfect. By 08CR represent their derived transition by a chain map alpha.
   Both bottom homologies are their a-th terms, so H^a(alpha) is alpha.f a.
   This is invertible because the derived transition is an isomorphism. After
   termwise pullback the bottom homology map is g*(alpha.f a), also invertible.
   Naturality of the flat-complex counit identifies this map with the derived
   transition after pullback. Thus the two local comparisons commute with the
   same transition on both sides and are equal as maps of the restricted sheaves.
   Affine opens cover the overlap, so equality holds on the entire overlap.
   Their inverses agree by uniqueness. Glue maps and inverses; both composites
   are identity since they are identity on each member of the inverse-image cover.
   Empty schemes are included; no separatedness is required.
   No perfection or universal-rank hypothesis is used in this homological step. -/
theorem localZeroBottomModel_pullback
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (T : Scheme.{u}) (D : schemeDerivedCategory T) (a : ℤ)
    (hmodel :
      ∀ t : T, ∃ U : T.Opens, t ∈ U ∧
      ∃ K : CochainComplex
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) ℤ,
        (∃ c : ℤ, ∀ i : ℤ, c < i → IsZero (K.X i)) ∧
        (∀ i : ℤ, i < a → IsZero (K.X i)) ∧ K.d a (a + 1) = 0 ∧
        (∀ i : ℤ, ∃ n : ℕ, Nonempty (K.X i ≅ SheafOfModules.free
          (R := moduleRings U.toScheme.toRingedSpace) (ULift.{u} (Fin n)))) ∧
        Nonempty ((derivedPullback U.ι).obj D ≅ DerivedCategory.Q.obj K))
    (T' : Scheme.{u}) (g : T' ⟶ T) :
    Nonempty
      ((Modules.tensorPullback g).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj D) ≅
        (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
            ((derivedPullback g).obj D)) := by sorry

end AlgebraicGeometry.Scheme
