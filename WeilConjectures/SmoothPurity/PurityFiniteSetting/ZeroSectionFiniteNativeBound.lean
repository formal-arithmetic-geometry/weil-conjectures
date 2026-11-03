/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.ZeroSectionCoefficientSupport

/-! # Finite native zero-section local vanishing

Source: the native-coefficient refinement of Step 3 in the current blueprint
`part-duality-trace-formula/sec-smooth-purity/sec-the-trace-map-of-affine-space/
sk-prop-an/thm-pur-localized-top-chern.proof.md`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.ProEtale
open AlgebraicGeometry.ProEtale.CondensedRing
open scoped CategoryTheory.Obj
namespace WeilConjectures.PurityFiniteSetting

/-- The finite native zero-section bound is the local geometric input.
Source: the finite affine zero-section purity comparison and its finite encoding,
Step 3 of `lem-pur-zero-section-bottom-coefficients`.
Proof: use `VectorBundleZeroSection.finite_type_frames` to choose a finite affine
Zariski cover and frames identifying each restricted zero section with the origin
in affine space. Restriction to an open is exact and has exact extension by zero
as left adjoint. It therefore preserves K-injectives and identifies the restricted
actual support functor with support along the restricted section. The normalized
finite coefficient encoding identifies the root line with the ordinary finite
Kummer line. Its tensor comparison identifies their positive rank powers and the
shift. Derive its exact closed-direct-image square and conjugate the native and
ordinary closed-support adjunctions to identify their right adjoints. Finite
affine-space zero-section purity now identifies each local supported input with
the coefficient unit in degree zero. Consequently each negative cohomology sheaf
restricts to zero on the frame cover and is zero by the sheaf axiom. The argument
uses only local support-object isomorphisms, with no chosen global Thom arrow.
Rank zero uses the unit and the empty base has the empty cover.
(blueprint: lem-pur-zero-finite-encoded-support-bound). -/
theorem nativeZeroSupport_finite_bound
    {P : PurityFiniteSetting.{u}} {B : Scheme.{u}}
    {hB : B ⟶ Spec (.of P.field.k)}
    [IsSeparated hB] [LocallyOfFiniteType hB] [QuasiCompact hB] {r : ℕ}
    (V : PurityVectorBundle P B hB r)
    (A : CommRingCat.{0}) (fin : Finite A) (n : ℕ)
    (hA : (P.coefficients.l ^ (n + 1) : A) = 0) :
    (nativeZeroSupport V (.finite A fin n hA)).IsGE 0 := by
  sorry

end WeilConjectures.PurityFiniteSetting
