/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.CategoryTheory.SpectralObjectBottomPageMap

/-! # Compatibility of a bottom-page map with passage to homology

Source: Stacks Project, Tags 012K and 015N; spectral-object page construction.
(blueprint: lem-sc-spectral-object-bottom-page-compatibility)
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits ComposableArrows

namespace CategoryTheory.Abelian.SpectralObject

/-- The cycles-to-homology square commutes with the bottom-page map to the abutment.
Source: Stacks Project, Tags 012K and 015N; expanded in Mathlib's spectral-object
`SpectralSequence.homologyData` and `spectralSequence_iso`.
(blueprint: lem-sc-spectral-object-bottom-page-compatibility)

Proof: Write a = 2-r and c = r-1. The page-r term is
E^p(a,0,1,c), and the successor is E^p(a-1,0,1,c+1). In the
spectral-object homology data, the kernel object is E^p(a-1,0,1,c).
Its inclusion into page r is the map changing a-1 to a followed by the
inverse page comparison, and its projection to the successor-page model
is the map changing c to c+1. Rewrite the spectral-sequence homology
isomorphism using these data. The standard cycles isomorphism identifies
both sides of the claimed equality with maps out of that kernel object.
Naturality of iota-E in its first interval makes the left composite equal
to iota-E from the kernel object followed by fromOpcycles at c. Naturality
of iota-E in its last interval makes the right composite equal to the same
iota-E followed by the opcycles map for c to c+1 and fromOpcycles at c+1.
The opcycles/fromOpcycles identity replaces the latter two maps by
fromOpcycles at c followed by H^p(0,c) to H^p(0,c+1). Finally the square
of H-maps for (bottom,c) to (bottom,c+1) and (0,c) to (0,c+1) commutes.
The vertical maps are isomorphisms because H^p(bottom,0) and
H^(p+1)(bottom,0) vanish. Move their inverses across this square;
functoriality of H identifies either final composite to H^p(bottom,top).
This proves the equality. For r=2 the first interval is the identity,
and for p=0 the degree p-1 is -1; both are covered by the same homology
data and vanishing statements, with no exceptional case.
-/
theorem bottomPageMap_compatibility
    {C : Type u} [Category.{v} C] [Abelian C]
    (Y : SpectralObject C EInt) [Y.IsFirstQuadrant]
    (p : ℕ) (r : ℤ) (hr : 2 ≤ r) :
    (Y.E₂SpectralSequenceNat.page r hr).iCycles (p, 0) ≫ Y.bottomPageMap p r hr =
      (Y.E₂SpectralSequenceNat.page r hr).homologyπ (p, 0) ≫
        (Y.E₂SpectralSequenceNat.iso r (r + 1) (p, 0) rfl hr).hom ≫
          Y.bottomPageMap p (r + 1) (by omega) := by sorry

end CategoryTheory.Abelian.SpectralObject
