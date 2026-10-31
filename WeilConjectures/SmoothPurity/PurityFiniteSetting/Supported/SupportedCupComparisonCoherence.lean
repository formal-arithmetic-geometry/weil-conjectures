/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels

/-! # Coherence of comparison with supported operations

Source: Stacks Project, Tags 09B1, 099V, 099W and 09XP.
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace WeilConjectures.PurityFiniteSetting

/-- The pullback, cup, Kummer and boundary comparison equations.

Source: Stacks Project, Tags 09B1, 099V, 099W, 09XP and 03PL; supported
functoriality proof Steps 6--8.
(blueprint: lem-pur-supported-cup-comparison-coherence).

Proof: The pseudofunctorial pullback square for the exact comparison inverse image
respects the constant coefficient unit. The closed-source exchange is uniquely
determined by its epic restriction map, while the open-source exchange is uniquely
determined by its monic inclusion. Their two composites in the comparison/pullback
square therefore agree. The signed Tate pullback comparison is its defining mate.
Apply the exact-functor single and shift comparison equations to these three
endpoint squares. Conjugating the derived Hom maps gives the supported, ordinary
and open pullback equalities. For cup compatibility, the same restriction of
local constant sections identifies the closed coefficient multiplications.
Normalized primitive roots identify the Tate multiplications. Flat degree-zero
tensor comparison identifies the corresponding derived coefficient maps, and
naturality of the shifted tensor comparison identifies their cup composites,
with the identical integral-degree sign on both sites. The root coefficient map
in the prescribed Kummer extension is the comparison root map. Naturality of
that exact power sequence therefore identifies its connecting class, including
the full-support direct-image unitor. Finally, the normalized closed-source
and open-source comparisons form an isomorphism from the comparison image of
the actual short exact coefficient sequence to the pro-etale sequence. Apply
naturality of its single-delta triangle, then compose with the class and use
exact inverse image compatibility with shifted composition. This is precisely
the asserted boundary equation, with the actual single-delta sign. All steps
respect empty and full support, zero coefficients, and negative cohomological
degrees. -/
theorem supportedCupComparisonCoherence (P : PurityFiniteSetting.{u}) :
    P.FunctorialCupComparisonPullback ∧ P.FunctorialCupComparisonOrdinaryPullback ∧
      P.FunctorialCupComparisonOpenPullback ∧ P.FunctorialCupComparisonCup ∧
      P.FunctorialCupComparisonKummer ∧ P.FunctorialCupComparisonBoundary := by
  sorry

end WeilConjectures.PurityFiniteSetting
