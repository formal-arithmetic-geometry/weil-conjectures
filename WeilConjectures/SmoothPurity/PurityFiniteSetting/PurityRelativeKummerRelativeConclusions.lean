/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.PurityRelativeKummerDefs
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Shift
public import WeilConjectures.SixFunctors.ProEtale.Comparison.LowerStarAcyclic
public import WeilConjectures.SixFunctors.ProEtale.BaseChange.SmoothBaseChange
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-! Relative conclusions assembled from normalized geometric stalks. -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace WeilConjectures.PurityFiniteSetting

/-- Relative unit, generator and vanishing conclusions over an arbitrary base scheme,
given the conclusions on its geometric points.
Source: blueprint prop-pur-gm-relative-kummer, Step 2 (stalk conservativity)
(blueprint: lem-pur-relative-kummer-relative-conclusions).

Proof: the projections p and pi are affine, hence qcqs, so by
lem-pur-relative-kummer-site-normalization the pro-etale direct images, units and the edge
generator are the comparison images of the etale ones, and it suffices to check every clause
on etale cohomology sheaves. Etale geometric stalks are conservative. At a geometric point
s : Spec Omega -> B, lem-pur-relative-kummer-normalized-stalks (with the strict-local
invariance it rests on) identifies the stalks at s of R p_* and R pi_* and of the unit and
Kummer edge maps with the corresponding derived global sections over Spec Omega, i.e. with
the conclusions over the base Spec Omega, which hold by `hgeom`. Hence every unit and the
generator map is an isomorphism on all stalks and the higher cohomology sheaves vanish. -/
theorem relative_kummer_relative_conclusions (P : PurityFiniteSetting.{u})
    (h : P.ramificationIndex ∣ P.level) (B : Scheme.{u})
    (p : B ⟶ Spec (CommRingCat.of P.field.k))
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (s : Spec (CommRingCat.of Ω) ⟶ B),
      P.RelativeKummerConclusions h (Spec (CommRingCat.of Ω))
        (s ≫ p)) :
    P.RelativeKummerConclusions h B p := by
  sorry

end WeilConjectures.PurityFiniteSetting
