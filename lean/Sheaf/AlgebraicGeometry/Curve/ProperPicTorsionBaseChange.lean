/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group T1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.AlgebraicGeometry.Picard.Group

import Sheaf.AlgebraicGeometry.BaseChangeCurve
import Sheaf.AlgebraicGeometry.GenusInvariant
import Sheaf.AlgebraicGeometry.Curve.ProperProjective
import Sheaf.AlgebraicGeometry.Curve.PicardDecomposition
import WeilConjectures.AlgebraicGeometry.Picard.Jacobian
import WeilConjectures.AlgebraicGeometry.AbelianVariety.Final

/-!
# Proper Picard torsion under algebraically closed extension

Source: blueprint sec-curve-estimates/sk-prop-ext-invariance, proper case in degree one
(blueprint: lem-sc-proper-pic-torsion-base-change).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme

namespace AlgebraicGeometry

/-- Source: blueprint sec-curve-estimates/sk-prop-ext-invariance, proper case in degree one
(blueprint: lem-sc-proper-pic-torsion-base-change).

Proof: the degree map takes values in the torsion-free group of integers, so an n-torsion
line bundle has degree zero. The representing Jacobian identifies degree-zero line bundles
with rational points and respects the group law. Jacobian base change identifies the
Jacobian of the base-changed curve with the scalar extension of the original Jacobian,
and its classifying-morphism equation identifies Picard pullback with extension of points.
As n is invertible, Jacobian n-torsion is finite etale. Over an algebraically closed field
such a scheme is a disjoint union of rational points; extending the field preserves exactly
these points. Thus the extension map on Jacobian n-torsion is bijective, and so is the map
on Picard n-torsion. In particular n = 1 gives the bijection of singleton identity groups.
No choice of bases or comparison of cardinalities is used to identify the canonical map. -/
theorem IsConnectedCurve.proper_pic_torsion_baseChange_bijective
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsProper f]
    (n : ℕ) [NeZero n] (_hn : (n : k) ≠ 0) :
    ∃ F : {L : C.Pic // L ^ n = 1} →
        {L : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).Pic // L ^ n = 1},
      Function.Bijective F ∧ ∀ L, (F L).val = Scheme.Pic.map
        (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) L.val := by sorry

end AlgebraicGeometry
