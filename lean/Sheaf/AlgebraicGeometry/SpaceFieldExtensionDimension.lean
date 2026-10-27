/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group NQ
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpace
public import Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.ProperCurveModuli
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Field.Defs
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.Topology.KrullDimension
import Sheaf.AlgebraicGeometry.SpaceLocalPropertiesChartTest
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeAffineCovers
import WeilConjectures.AlgebraicGeometry.DimensionBaseChange
import WeilConjectures.AlgebraicGeometry.DimensionAffineOpenCover
import WeilConjectures.AlgebraicGeometry.Dimension
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # Dimension of an algebraic space under a field extension

Source: Stacks Project, Morphisms of Spaces, Tag 04NS(1), with Decent Spaces,
Tags 0A4J and 088J (blueprint: lem-sfb-space-field-extension-dimension).

On schemes over Spec k the terminal presheaf represents Spec k. Thus the presheaf
pullback along the terminal map from h_(Spec K) is the actual base change Y_K.
Both dimensions use the existing field-valued point classes with their atlas topology.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- A separated finite-type algebraic space over a field has unchanged topological
Krull dimension after any extension of that field. Empty spaces are included.

Source: Stacks Project, Morphisms of Spaces, Tag 04NS(1); Decent Spaces,
Tags 0A4J and 088J (blueprint: lem-sfb-space-field-extension-dimension).

Proof:
1. The closed diagonal is quasi-compact on scheme tests, since the inverse image of a
   quasi-compact open under a closed immersion is a closed subset of that open. Hence
   the separated space is quasi-separated [def-weil-closed-immersion].
2. Choose a surjective etale scheme atlas U of Y [def-trf-algebraic-space]. Its structure
   map is locally of finite type by [lem-sfb-space-local-properties-chart-test]. The
   pullback atlas is U_K, by [lem-trf-space-fibre-products-etale-covers] and the compatible
   pair universal property [def-pc-fibre-product]. Apply
   [lem-sfb-space-etale-atlas-topological-dimension] to identify the two space dimensions
   with those of U and U_K. This is the atlas reduction in Tag 04NS, with Tags 0A4J/088J.
3. If U is empty, U_K is empty and both dimensions are bottom
   [def-kun-topological-krull-dimension]. Otherwise
   [lem-pc-dim-base-change-affine-covers] supplies matching affine covers Spec A_i and
   Spec (A_i tensor_k K), with each A_i finite type over k.
4. Apply the ring clause of [lem-pc-dim-base-change] on each chart. The affine-cover
   supremum formula [lem-pc-dimension-affine-open-cover] and the comparison
   [lem-pc-scheme-dimension-local-rings] give equal topological dimensions for U_K and U.
   Substitute the atlas equalities. No separability, algebraicity or nonemptiness is used.
-/
theorem topologicalKrullDim_field_extension (k K : Type u)
    [Field k] [Field K] [Algebra k K] (Y : AlgebraicSpace (Spec (.of k)))
    (hsep : IsRepresentableWith (fun _ _ p ↦ IsClosedImmersion p.left)
      (prod.lift (𝟙 Y.obj.obj) (𝟙 Y.obj.obj)))
    (hqc : MapIsQuasiCompact (terminal.from Y.obj.obj))
    (hlft : ∀ (U : Over (Spec (.of k))) (a : yoneda.obj U ⟶ Y.obj.obj),
      IsEtale a → LocallyOfFiniteType U.hom) :
    topologicalKrullDim (Point (Limits.pullback (terminal.from Y.obj.obj)
      (terminal.from (yoneda.obj
        (Over.mk (Spec.map (CommRingCat.ofHom (algebraMap k K)))))))) =
      topologicalKrullDim (Point Y.obj.obj) := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
