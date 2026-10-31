/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AssociatedLogPresentation
import WeilConjectures.RingTheory.FilteredRingLogPushout
import WeilConjectures.CategoryTheory.CommutativeMonoidSheafification
import Mathlib.CategoryTheory.Sites.Point.Skyscraper

/-!
# Normalized stalks of an associated-log presentation

Source: ILO VI 1.1, p.69; Stacks Tags 04AX, 03PQ and 03PT.
(blueprint: lem-trf-associated-log-presentation-stalk-comparison).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- A presented associated log structure has the canonical pushout stalks and its
canonical global monoid map is a chart.

Source: ILO VI 1.1, p.69; Stacks Tags 04AX, 03PQ and 03PT. This is the
normalization step in the associated-log construction, not its existence or its
universal mapping property.

Proof: use the opposite category of pointed étale neighbourhoods to compute both
ring and monoid stalks. Pass to its small filtered final model, on which
`filteredRing_logPushout` applies. A ring unit is represented by a stage unit:
represent it and its inverse and realize their product equation on a common
refinement. If a chart element becomes a unit in the ring stalk, the same
argument makes it a unit on a refinement of any given stage. Consequently the
quotient of stalk pairs maps isomorphically to the stalk of the quotient presheaf.
The forward map sends every pair with a represented unit to that pair's germ;
the inverse chooses a stage unit representative, and independence follows by
realizing equality on a common refinement. A relation involving a chart element
is already a stage relation after refining until its image is a unit. Both maps
preserve products, computed at common stages, and their composites fix all pairs.
Monoid sheafification has the underlying set sheafification, which preserves
geometric stalks. Compare the given sheafification unit with that sheafification
by uniqueness to obtain the stated isomorphism with exactly the indicated germ
formula. Its structural map sends [r,a] to beta_t(r)a. In particular [1,a] is the
unique log unit above a, and [r,1] is the germ of the canonical global chart.
Thus the pair map of this chart is the quotient map followed by this isomorphism:
it is surjective with precisely the generated pushout congruence as kernel. This
is `IsStalkChart` at the terminal pointed neighbourhood. Naturality of germs gives
the same assertion for any lift into the terminal object, proving `IsChart`.
No finite generation, cancellation or injectivity of beta is used.
(blueprint: lem-trf-associated-log-presentation-stalk-comparison). -/
theorem associatedLog_presentation_stalk_comparison {X : Scheme.{max u v}}
    [IsLocallyNoetherian X] {R : Type v} [CommMonoid R] (β : R →* Γ(X, ⊤))
    (L : EtaleLogStructure.{max u v} X) (η : associatedLogPresheaf β ⟶ L.monoidSheaf.obj)
    (hη : IsAssociatedLogPresentation β L η) :
    (∀ (Ω : Type (max u v)) [Field Ω] [IsAlgClosed Ω]
        (t : Spec (.of Ω) ⟶ X),
        ∃ e : divisorialChartPushout (P := ULift.{u, v} R)
          (associatedLogStalkBeta β t).mrangeRestrict ≅
            L.toEtalePrelogStructure.stalk t,
          ∀ (W : X.Etale) (w : (Scheme.pointSmallEtale t).fiber.obj W)
            (r : R) (a : Γ(W.left, ⊤)ˣ),
            e.hom ((divisorialChartCongruence (P := ULift.{u, v} R)
              (associatedLogStalkBeta β t).mrangeRestrict).mk'
                (ULift.up r, Units.map (strictLocalGerm X t W w).hom.toMonoidHom a)) =
              L.toEtalePrelogStructure.germ t W w
                (η.app (op W) ((divisorialChartCongruence (P := ULift.{u, v} R)
                  (associatedLogBetaLift β W).mrangeRestrict).mk' (ULift.up r, a)))) ∧
    L.IsChart (Scheme.Etale.mk (𝟙 X)) (associatedLogIota β L η) := by
  sorry

end AlgebraicGeometry
