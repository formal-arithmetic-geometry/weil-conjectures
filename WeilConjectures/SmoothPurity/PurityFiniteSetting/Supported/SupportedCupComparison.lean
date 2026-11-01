/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupFunctorialityModels
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupComparisonBasic
import WeilConjectures.SmoothPurity.PurityFiniteSetting.Supported.SupportedCupComparisonCoherence

/-! # Supported cup comparison between the two small sites

Source: Stacks Project, Tags 09B1, 099V, 099W and 09XP.
-/

@[expose] public section
set_option autoImplicit false
universe u
namespace WeilConjectures.PurityFiniteSetting

/-- Supported cup comparison between the two small sites.

Source: Stacks Project, Tags 09B1, 099V, 099W and 09XP; supported functoriality proof steps
6--8.
(blueprint: lem-pur-supported-cup-comparison-calculus).

Proof: The exact comparison inverse image is fully faithful on finite coefficients;
conjugating its derived Hom map by the specified source and Tate isomorphisms
proves the three bijectivity fields. Its pseudofunctorial pullback square and
naturality of the source, constant, open and Tate comparisons give the three
pullback fields. On local constant sections the comparison preserves closed
restriction and multiplication; the same is true of the signed Tate line
multiplication. Flat degree-zero tensor comparison and naturality of the total
tensor shift isomorphism therefore identify the two prescribed cup composites.
The root coefficient map in the defining Kummer prescription is exactly the
comparison root map, so its connecting class is identified as well. The closed
source comparison is normalized by restriction; the open comparison is the
unique kernel isomorphism normalized by inclusion. These equations imply the
forget_support and open_restriction fields. Together they form an isomorphism
from the exact comparison image of the actual open/closed short exact sequence
to the pro-etale sequence. Naturality of its single-delta triangle gives the
boundary field with precisely the single-delta sign convention. This argument
also covers full support, empty support, the zero coefficient ring and negative
degrees. -/
theorem supportedCupComparison (P : PurityFiniteSetting.{u}) : P.FunctorialCupComparisonLaws := by
  obtain ⟨hs, ho, hu, hf, hr⟩ := supportedCupComparisonBasic P
  obtain ⟨hp, hop, hup, hc, hk, hb⟩ := supportedCupComparisonCoherence P
  exact {
    supported_bijective := hs
    ordinary_bijective := ho
    open_bijective := hu
    pullback := hp
    ordinary_pullback := hop
    open_pullback := hup
    cup := hc
    kummer := hk
    forget_support := hf
    open_restriction := hr
    boundary := hb
  }

end WeilConjectures.PurityFiniteSetting
