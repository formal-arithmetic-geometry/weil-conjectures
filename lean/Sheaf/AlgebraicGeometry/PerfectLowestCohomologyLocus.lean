/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group E1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.AlgebraicGeometry.DerivedTensorCohomologyVanishes
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation

/-! # The locally closed locus of free lowest cohomology of a perfect complex

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.31.4, Tag 0BDL
(blueprint: lem-sc-perfect-h0-locally-closed).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

set_option autoImplicit false

namespace AlgebraicGeometry.Scheme

/-- A perfect complex of Tor amplitude `[a,b]` has a finitely presented immersion
representing universal finite local freeness of its degree-`a` derived pullback cohomology.
On this locus the degree-`a` cohomology is finite locally free of rank `r`, and its
pullback to every scheme over the locus is the degree-`a` cohomology of the composite
pullback. Finite presentation is `LocallyOfFinitePresentation` together with `QuasiCompact`.
Source: Stacks Project, Derived Categories of Schemes, Lemma 36.31.4, Tag 0BDL
(blueprint: lem-sc-perfect-h0-locally-closed).

Proof:
1. The fibre dimensions `β_i` are upper semicontinuous, locally constructible and
   invariant under base change (lem-sc-perfect-jump-loci). Restrict to the open locus
   `β_a ≤ r`; every map satisfying the universal freeness condition factors through it.
2. At a point with `β_a = r`, choose an affine finite-free residue model
   (lem-sc-perfect-finite-free-residue-model). Tor amplitude makes the terms below
   `a` zero. The term in degree `a` has rank `r`. Vanishing of the entries of its outgoing
   matrix defines a closed subscheme with free degree-`a` cohomology of rank `r`.
   Points with `β_a < r` have open neighbourhoods disjoint from the desired locus.
3. Maps through the matrix-zero locus retain zero matrix after every base change.
   Conversely, the universal condition gives fibre rank `r`. Locally on an affine
   source, the kernel `K` of the outgoing matrix is free of rank `r`. The inclusion
   `K → B^r` is an injective square free map, and the dual of its cokernel is zero
   (lem-sc-square-injective-free-map-dual-coker-zero). Its cokernel injects into the
   target free module via the outgoing matrix. Every coordinate projection is zero,
   so that matrix is zero; the map therefore factors through the closed subscheme.
4. The finitely many matrix entries give a finite type ideal, hence finite presentation
   of the immersion. On the locus the complex has no preceding term and zero outgoing
   differential in degree `a`. Its cohomology is its rank-`r` term, and pulling back
   this same model gives the asserted pullback identification.
5. On overlaps the local closed subschemes represent the same functor of maps from
   step 3. Their unique identifications glue, giving the required immersion. -/
theorem exists_perfectLowestCohomologyLocus
    [∀ T : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings T.toRingedSpace))]
    (S : Scheme.{u})
    [∀ U : S.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over U))]
    (E : schemeDerivedCategory S) (hE : IsPerfect S E) (a b : ℤ)
    (hamp : ∀ F : SheafOfModules.{u} (moduleRings S.toRingedSpace),
      ∀ i : ℤ, i < a ∨ b < i → schemeDerivedTensorCohomologyVanishes S E F i)
    (r : ℕ) :
    ∃ (Z : Scheme.{u}) (j : Z ⟶ S),
      IsImmersion j ∧ LocallyOfFinitePresentation j ∧ QuasiCompact j ∧
      (∀ (T : Scheme.{u}) (h : T ⟶ S),
        (∃ g : T ⟶ Z, g ≫ j = h) ↔
          ∀ (T' : Scheme.{u}) (u' : T' ⟶ T),
            SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings T'.toRingedSpace)) a).obj
                  ((derivedPullback (u' ≫ h)).obj E)) r) ∧
      SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) a).obj
            ((derivedPullback j).obj E)) r ∧
      (∀ (T : Scheme.{u}) (g : T ⟶ Z),
        Nonempty
          ((Modules.tensorPullback g).obj
              ((DerivedCategory.homologyFunctor
                (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) a).obj
                  ((derivedPullback j).obj E)) ≅
            (DerivedCategory.homologyFunctor
              (SheafOfModules.{u} (moduleRings T.toRingedSpace)) a).obj
                ((derivedPullback (g ≫ j)).obj E))) := by
  sorry

end AlgebraicGeometry.Scheme
