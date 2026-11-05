/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.ThmPeIndetaleRefinementPart2Supplement
public import WeilConjectures.RingTheory.EtaleContraction.ThmPeIndetaleRefinementPart1
public import WeilConjectures.ProperBaseChange.PrincipalWLocalization.Retained.ThmPeIndetaleRefinementPart2Supplement3

/-! # The strict w-local cover

Source: blueprint, sec-proper-base-change/sk-thm-properbasechange, order 1228,
"The strict w-local cover" (blueprint: def-weil-pbc-strict-w-cover).

We compose the recorded finite-partition w-localization, étale contraction, and retained
localization. The final algebra structure is given by the composite of their structural maps.
-/

@[expose] public section

universe u

namespace PrincipalWLocalization.StrictWCover

variable (A : Type u) [CommRing A]

end PrincipalWLocalization.StrictWCover
