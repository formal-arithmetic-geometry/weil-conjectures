/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Compactification.Dense
public import WeilConjectures.Mathlib.AlgebraicGeometry.Gluing

/-!

# Compactifications which are isomorphisms over an open

Let `F : A ⟶ Z` be a separated, quasi-compact morphism locally of finite type to a
quasi-compact quasi-separated scheme, and let `ι : V ⟶ Z` be a quasi-compact open immersion
over which `F` is an open immersion: `F ⁻¹ V ⟶ V` is an open immersion. Then `F` factors as an
open immersion `A ⟶ B` followed by a proper morphism `p : B ⟶ Z` which is an isomorphism over
`V` (`AlgebraicGeometry.exists_isProper_isPullback_of_isOpenImmersion`).

The construction glues `A` and `V` along `F ⁻¹ V` (a pushout of open immersions), which is
separated over `Z` since the graph of `F ⁻¹ V ⟶ V` is an isomorphism, takes a dense
compactification `B` of the glued scheme over `Z` (Nagata), and observes that the section
`V ⟶ p ⁻¹ V` is an open and closed immersion with dense image, hence an isomorphism.

More generally, `V` may be a closed subscheme of an open `Z° ⊆ Z` containing the image of
`F ⁻¹ Z°` (`AlgebraicGeometry.exists_isProper_isPullback_of_isClosedImmersion`): then `B` is `V`
over `Z°`, and `A ∪ V` is dense in `B`. Such density statements identify inverse images of opens
(`AlgebraicGeometry.isPullback_id_of_dense`): an open `N ⊆ B` over an open `N ⊆ X` along a
separated `B ⟶ X` is the whole inverse image as soon as a dense subset of `B` meets the inverse
image only in `N`, the section `N ⟶ B ×_X N` being open, closed and dense.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {A A' V Z : Scheme.{u}} {F : A ⟶ Z} {ι : V ⟶ Z} {a : A' ⟶ A} {F' : A' ⟶ V}

end AlgebraicGeometry
