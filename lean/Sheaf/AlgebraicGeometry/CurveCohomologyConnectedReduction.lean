/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
import Sheaf.AlgebraicGeometry.BaseChangeCurve
import Sheaf.Paper.FiniteCoproductCohomologyAssembly

/-! # Reduction of curve comparison to connected curves

Source: blueprint sk-prop-ext-invariance, first step (clopen connected components).
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry

/-- Comparison on connected smooth curves implies comparison on every qc smooth
separated curve of relative dimension one.
Source: blueprint sk-prop-ext-invariance, first step.
(blueprint: lem-sc-curve-cohomology-connected-reduction)

Proof: C is finite type over k and hence Noetherian. Smoothness makes it regular,
so its finitely many connected components are open and closed, integral, and of
pure dimension one. Their structure morphisms are connected smooth curves.
Base change preserves their disjoint union, and each component remains connected
because k is algebraically closed. Cohomology of a finite disjoint union is the
product of the component cohomologies, naturally for the canonical pullback map
and the inverse image of the constant sheaf. Apply h to each component and take
the product of the resulting bijections. The product over no components handles
C empty. No comparison assertion for a connected curve is proved by this reduction;
it is precisely the supplied hypothesis. -/
theorem bijective_curve_cohomologyMap_of_connected
    {k K : Type u} [Field k] [Field K] [IsAlgClosed k] [IsAlgClosed K] [Algebra k K]
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k))
    [SmoothOfRelativeDimension 1 f] [IsSeparated f] [QuasiCompact f]
    (n q : ℕ)
    (h : ∀ {D : Scheme.{u}} (g : D ⟶ Spec (.of k)) [IsConnectedCurve g] [Smooth g],
      Function.Bijective (Etale.cohomologyMap
        (pullback.fst g (Spec.map (CommRingCat.ofHom (algebraMap k K))))
        (D.constantZMod n) q)) :
    Function.Bijective (Etale.cohomologyMap
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (C.constantZMod n) q) := by sorry

end AlgebraicGeometry
