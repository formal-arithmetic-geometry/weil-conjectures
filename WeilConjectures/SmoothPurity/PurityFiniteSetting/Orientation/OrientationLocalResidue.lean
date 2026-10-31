/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Affine.PurityAffineLineOrientationData

/-! # The normalized residue in a geometric affine-line chart

Source: blueprint affine-line orientation, rank-one normalization; Milne, Section 16
(blueprint: lem-pur-orientation-local-residue).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open AlgebraicGeometry.ProEtale AlgebraicGeometry.ProEtale.RetractedSupport

namespace WeilConjectures.PurityFiniteSetting

/-- A geometric affine line admits the published support chart, with residue one on
its coordinate boundary. This local statement has no global base or orientation map.

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/
sk-prop-a1-kummer/thm-pur-affine-line-orientation.proof.md, rank-one normalization;
Milne, Proposition 14.3, Example 16.3 and Theorem 16.7
(blueprint: lem-pur-orientation-local-residue).

Proof: Put N=P.kummerLevel. The finite Kummer-level theorem gives N>=1 and ell^N A=0.
Apply rankOne_local_calculation to Spec Omega over k and its identity geometric point.
Its coefficient map sends a root z to z tensor 1 and its pro-etale support residue
sends the snake boundary of the coordinate class to 1. Use the canonical comparison
between right-derived sheaf functors and homology of the total derived functor on a
single sheaf, and identify the punctured basic open with the zero-section complement.
Their restriction maps agree; naturality of the injective-resolution comparison
identifies their kernel complexes and snake boundaries. The root-line identification
is the finite Kummer comparison, so it carries the actual coordinateKummer class,
rather than an unspecified generator. Construct the Gysin chart from the localization
triangle of the retracted zero section: on this geometric line the adjacent ordinary
cohomology calculations give a degree-zero exceptional value after shifting by two.
The global edge is consequently invertible, and the counit-normalized support
comparison gives the chart's support isomorphism and its required formula. Choose its
boundary from the same injective snake construction, giving exactness and normalization.
Transport the rank-one pro-etale residue through the preceding canonical comparisons.
Its value on the chart coordinate boundary is 1, since ord_0(t)=1. All constructions
are over Omega itself; finite type of Omega over k is never assumed. -/
theorem orientation_local_residue (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level)
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω] [Algebra P.field.k Ω] :
    ∃ D : OrientationSupportData P h (Spec (CommRingCat.of Ω)),
    ∃ ρ : P.gysinSupport h (Spec (CommRingCat.of Ω)) ≅
        ModuleCat.of P.Coefficient P.Coefficient,
      ρ.hom (D.coordinateBoundary P h
        (Spec.map (CommRingCat.ofHom (algebraMap P.field.k Ω)))) = 1 := by sorry

end WeilConjectures.PurityFiniteSetting
