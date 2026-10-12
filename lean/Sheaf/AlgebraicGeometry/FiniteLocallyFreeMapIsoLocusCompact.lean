/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group K1
-/
module

public import Sheaf.AlgebraicGeometry.ModuleMapIsoLocus
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Affine compactness of the isomorphism locus

Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3), and Tag 0BDP, final sentence.
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- On an affine open, the locally invertible locus of a vector bundle map is compact.
Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3), and Tag 0BDP, final sentence.
(blueprint: lem-sc-finite-locally-free-map-iso-locus-compact)

Proof: Cover the affine open V by simultaneous finite free frames for M and N, refining
these frames to principal affine opens of V. Compactness of V gives a finite subcover.
On each frame with equal ranks, the locally invertible locus is the principal open of
its matrix determinant: the adjugate divided by the determinant is an inverse, and any
inverse forces the determinant to be a unit. On a frame with unequal ranks the locus
is empty, since an inverse at any point would give an isomorphism of residue vector
spaces of unequal dimensions. Thus the intersection with V is a finite union of
principal affine opens and is compact. The identification with moduleMapIsoLocus uses
its neighbourhood definition: every determinant open has an inverse; conversely,
invertibility on any neighbourhood implies invertibility on its stalks and hence the
same determinant condition. In rank zero the determinant is 1. Empty frames contribute
nothing, and no reducedness or global bound on the varying ranks is required. -/
theorem isCompact_moduleMapIsoLocus_inter {W : Scheme.{u}} (M N : W.Modules)
    [M.IsFiniteLocallyFree] [N.IsFiniteLocallyFree] (φ : M ⟶ N)
    (V : W.Opens) (hV : IsAffineOpen V) :
    IsCompact ((V : Set W) ∩ (moduleMapIsoLocus φ : Set W)) := by sorry

end AlgebraicGeometry.Scheme.Modules
