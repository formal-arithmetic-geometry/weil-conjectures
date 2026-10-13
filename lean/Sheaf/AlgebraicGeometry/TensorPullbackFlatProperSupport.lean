/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K3
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage
public import Sheaf.AlgebraicGeometry.ClosedSubsetProperOverBase
public import Sheaf.AlgebraicGeometry.TensorPullback
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs

/-! # Base change preserves flat finitely presented modules with proper support

Source: Stacks Project, Tags 01U8 (relative flatness), 056J (support), and 0CYS.
(blueprint: lem-pc-tensor-pullback-flat-proper-support).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Base change preserves finite presentation, base-flatness and proper support
for one module. The square must be cartesian; an arbitrary commutative square would
not preserve flatness over the new base.

Proof:
1. Pull back a local finite presentation of M. Tensor is right exact and sends
   finite free modules to finite free modules, giving finite presentation of p* M.
2. At a point of Xj, the cartesian square identifies p* M with the base change
   of a module flat over the old base (Tag 01U8). On affine cartesian charts,
   if A is the old base ring, B its scheme algebra, A' the new base ring,
   and N the module, then (B ⊗[A] A') ⊗[B] N ≅ A' ⊗[A] N.
   The right side is flat over A'. Localization preserves this flatness.
   These charts cover Xj, giving relative stalk flatness. For any affine test
   open U over an affine base open V, quasi-coherence identifies localizations
   of its section module with stalks. Each is flat over the corresponding
   localized base ring. The localization criterion of Tag 00HT(6) gives
   flatness of the section module over the base ring, precisely IsFlatOver.
3. M is finitely presented, hence quasi-coherent of finite type. Tag 056J identifies
   the support of p* M with the inverse image of the support of M. By Tag 0CYS,
   represent M on a closed subscheme proper over Si; base change that closed
   subscheme to Sj. Its morphism remains proper and the pulled-back module is
   supported there. Its support is closed by finite type and is proper over Sj,
   again by Tag 0CYS. This is precisely HasSupportProperOver fj.

Edge cases: the zero module has empty support and remains zero; an empty source
causes no exception. No flatness of k or p is required: only the square is cartesian.
Source: Stacks Project, Tags 01U8 (relative flatness), 056J (support), and 0CYS.
(blueprint: lem-pc-tensor-pullback-flat-proper-support).
-/
theorem tensorPullback_flat_proper_support
    {Xi Xj Si Sj : Scheme.{u}}
    (fi : Xi ⟶ Si) (fj : Xj ⟶ Sj) [LocallyOfFiniteType fi] [LocallyOfFiniteType fj]
    (p : Xj ⟶ Xi) (k : Sj ⟶ Si) (hcart : IsPullback p fj fi k)
    (M : Xi.Modules) [M.IsFinitePresentation]
    (hflat : M.IsFlatOver fi) (hproper : Scheme.Modules.HasSupportProperOver fi M) :
    (Scheme.Modules.tensorPullbackObj p M).IsFinitePresentation ∧
      (Scheme.Modules.tensorPullbackObj p M).IsFlatOver fj ∧
      Scheme.Modules.HasSupportProperOver fj (Scheme.Modules.tensorPullbackObj p M) := by sorry

end AlgebraicGeometry
