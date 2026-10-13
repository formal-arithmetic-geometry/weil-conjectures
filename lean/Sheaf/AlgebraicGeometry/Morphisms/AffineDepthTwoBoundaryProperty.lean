/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Sheaf.RingTheory.Depth
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
@[expose] public section
universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme
/-- The double-dual extension has depth at least two at boundary points.
Source: Stacks Project, Tag 0EY6 and the kernel calculation in its proof.
(blueprint: new-affine-depth-two-boundary-property)
The finite free presentation of the double dual makes multiplication by a
regular pair injective on the kernel; Nakayama gives the stated depth bound. -/
theorem affine_depth_two_boundary_property
    (A : CommRingCat.{u}) [IsNoetherianRing A] (W : (Spec A).Opens)
    (hboundary : ∀ x : Spec A, x ∉ W →
      (2 : ℕ∞) ≤ IsLocalRing.depth
        (R := (Spec A).presheaf.stalk x) ((Spec A).presheaf.stalk x))
    (H : (Spec A).Modules) (hqc : H.IsQuasicoherent)
    (hfin : ∀ V : (Spec A).Opens, IsAffineOpen V →
      Module.Finite ((Spec A).presheaf.obj (op V)) (H.val.obj (op V))) :
    ∀ x : Spec A, x ∉ W →
      ∃ hfinite : Module.Finite ((Spec A).presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x),
        letI := hfinite
        (2 : ℕ∞) ≤ IsLocalRing.depth (R := (Spec A).presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) H.val.presheaf x) := by sorry
end AlgebraicGeometry.Scheme
