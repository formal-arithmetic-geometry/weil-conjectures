/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.Modules.Invertible
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-!
# Cohomology of a sheaf placed in one degree

Source: blueprint `sec-picard-framework/sk-def-picard-f/lem-pc-degree-zero-properties.md`,
node lem-pc-degree-zero-properties, order 820 (blueprint: lem-pc-degree-zero-properties).

## Main statements

* `cohomology_of_iso_invertible_single_zero` computes the cohomology of an invertible sheaf
  placed in degree zero.
* `cohomology_of_iso_locallyFree_shift` computes the cohomology of a finite locally free
  sheaf shifted by `-i`.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An object isomorphic to an invertible sheaf in degree zero has that sheaf as its
zeroth cohomology and vanishing cohomology in every other degree.
Source: blueprint `sec-picard-framework/sk-def-picard-f/lem-pc-degree-zero-properties.md`,
first assertion (blueprint: lem-pc-degree-zero-properties).

Proof: (1) The given derived isomorphism preserves every cohomology sheaf: a zig-zag of
quasi-isomorphisms induces isomorphisms on cohomology. (2) The single complex has `N` in
 degree zero and zero in every other degree, so its zeroth cohomology is `N` and all its
other cohomology sheaves vanish. Transport these computations along the given isomorphism. -/
theorem cohomology_of_iso_invertible_single_zero (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : schemeDerivedCategory X) (N : X.Modules) [Scheme.Modules.IsInvertible N]
    (hM : Nonempty (M ≅ (DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj N)) :
    (∀ i : ℤ, i ≠ 0 → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj M)) ∧
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj M ≅ N) := by
  sorry

/-- An object isomorphic to a locally free sheaf of rank `r` shifted by `-i` has that sheaf
as its degree-`i` cohomology and vanishing cohomology in every other degree.
Source: blueprint `sec-picard-framework/sk-def-picard-f/lem-pc-degree-zero-properties.md`,
second assertion (blueprint: lem-pc-degree-zero-properties).

Proof: (1) The given derived isomorphism preserves all cohomology sheaves, since
quasi-isomorphisms do so. (2) The shift of the single degree-zero complex by `-i` has `E`
in degree `i` and zero in every other degree. (3) Its degree-`i` cohomology is therefore
`E` and its degree-`j` cohomology vanishes when `j ≠ i`. Transport these computations
along the given isomorphism. -/
theorem cohomology_of_iso_locallyFree_shift (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (M : schemeDerivedCategory X) (E : X.Modules) (r : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E r] (i : ℤ)
    (hM : Nonempty (M ≅ ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj E)⟦-i⟧)) :
    (∀ j : ℤ, j ≠ i → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) j).obj M)) ∧
    Nonempty ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj M ≅ E) := by
  sorry

end AlgebraicGeometry
