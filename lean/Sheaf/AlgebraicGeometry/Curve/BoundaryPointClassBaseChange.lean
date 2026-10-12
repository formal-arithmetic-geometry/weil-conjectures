/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import WeilConjectures.AlgebraicGeometry.Curve.Compactification
public import WeilConjectures.AlgebraicGeometry.Curve.Picard
public import WeilConjectures.Compactification.BaseChange

/-! # Boundary point classes under base change

Source: affine case of `thm-sc-constant-invariance`, boundary paragraph.
(blueprint: lem-sc-boundary-point-class-base-change).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Base change bijects the rational boundary points and pulls back their point classes.

Source: affine case of `thm-sc-constant-invariance`, boundary paragraph.
(blueprint: lem-sc-boundary-point-class-base-change).

Proof: the smooth connected curve c.Z is integral and noetherian of dimension one.
The nonempty open c.i(C) is dense, so its closed complement is a finite set of closed
points. These points have residue field k by algebraic closedness and finite type. Their
fibres after extension are Spec k', with one rational closed point.
The cartesian open-immersion square identifies the complement of the new open with these
fibres. Different fibres are disjoint, yielding the bijection. The invertible ideal of a
point pulls back to the invertible ideal of its fibre; flat pullback commutes with duals,
so the associated classes of O(P) agree. For a singleton boundary the bijection is unique;
an empty boundary gives the unique empty equivalence. -/
theorem boundary_point_class_base_change
    {k k' : Type u} [Field k] [Field k'] [Algebra k k'] [IsAlgClosed k] [IsAlgClosed k']
    {C : Scheme.{u}} (f : C ⟶ Spec (.of k)) [IsConnectedCurve f] [Smooth f] [IsAffine C]
    (c : Compactification f) [IsConnectedCurve c.g] [Smooth c.g]
    [hsm : SmoothOfRelativeDimension 1 c.g]
    [hsm' : SmoothOfRelativeDimension 1
      (c.baseChange (Spec.map (CommRingCat.ofHom (algebraMap k k')))).g]
    : let b := Spec.map (CommRingCat.ofHom (algebraMap k k'))
      let c' := c.baseChange b
      ∃ e : {P : closedPoints c.Z // P.val ∉ Set.range c.i.base} ≃
          {Q : closedPoints c'.Z // Q.val ∉ Set.range c'.i.base},
        ∀ P, Scheme.Pic.mapHom (pullback.fst c.g b)
          (@Scheme.Pic.ofClosedPoint k _ c.Z ⟨c.g⟩ hsm P.val) =
          @Scheme.Pic.ofClosedPoint k' _ c'.Z ⟨c'.g⟩ hsm' (e P).val := by sorry

end AlgebraicGeometry
