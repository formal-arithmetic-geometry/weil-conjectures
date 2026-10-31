/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ClosedTestDerivedExchangeMaps

/-! # Canonical section localization for arbitrary sources

Source: Stacks Project, sites-cohomology.tex, Tags 0D6E and 0D6F.
(blueprint: lem-sfb-nonaffine-proetale-section-localization). -/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ClosedTestSectionSteps

open ClosedTestDerivedExchangeModel

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The canonical Leray section comparison along a pro-etale test is natural
under maps of pro-etale tests.
Source: Stacks Project, Tags 0D6E and 0D6F
(blueprint: lem-sfb-nonaffine-proetale-section-localization).

Proof: identify internal modules with modules over the section-ring sheaf and use
condensed localization to identify inverse image along b with slice restriction.
Choose a K-injective representative I. Exact inverse image makes f_*I K-injective;
slice restriction preserves K-injectivity. The direct-image identity (f_*I)(W)=I(X×_U W)
and unbounded sections localization identify both sides with the same section complex.
The right-derived composition comparison is normalized by this ordinary identity.
Under the induced derived adjunction, the unit-square-counit formula defining
sectionComparison is precisely that comparison. Thus its components are invertible.
For a map a of tests, both composites are the presheaf restriction on I, with the
canonical pullback composition identifications. This proves TestNaturality after Q.
The argument permits arbitrary unbounded inputs, nonaffine sources and empty tests. -/
theorem proetale_section_localization
    {X U W : Scheme.{u}} (f : X ⟶ U) (b : W ⟶ U) [WeaklyEtale b] :
    ∀ {W' : Scheme.{u}} (b' : W' ⟶ U) [WeaklyEtale b']
        (a : W' ⟶ W) (ha : a ≫ b = b'), TestNaturality Λ f a ha := by sorry

end AlgebraicGeometry.ProEtale.ClosedTestSectionSteps
