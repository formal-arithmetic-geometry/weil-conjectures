/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group A2
-/
module

public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.OpenClosed.Conservative

/-!
# Jointly surjective pullbacks detect unbounded derived isomorphisms

Generalize the source-library geometric-point argument to arbitrary covering families.
This supplies a prerequisite for graph comparison without importing the projection formula.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- A jointly surjective family of scheme morphisms detects isomorphisms after derived
inverse image; the morphisms need not be etale.
Source: the cohomology argument of
`isIso_of_isIso_leftDerivedUpperStar_algClosurePoint_map` in the source projection-formula
module, and the sheaf theorem `isIso_of_isIso_upperStar_map_of_jointlySurjective`.
(blueprint: lem-etale-derived-jointly-surjective-conservative).

Proof: use the cohomology criterion for unbounded derived isomorphisms. Exact inverse
image commutes with every cohomology functor and agrees with left-derived inverse image.
The hypotheses thus make every cohomology morphism invertible after all family pullbacks.
The sheaf conservativity theorem for jointly surjective inverse images makes each of
these cohomology morphisms invertible. Empty sources and the empty base are included. -/
theorem isIso_of_isIso_leftDerivedUpperStar_map_of_jointlySurjective
    (A : Type (u + 1)) [CommRing A] {Y : Scheme.{u}}
    {ι : Type u} {U : ι → Scheme.{u}} (a : ∀ i, U i ⟶ Y)
    (ha : ∀ y : Y, ∃ (i : ι) (x : U i), (a i).base x = y)
    {M N : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))}
    (φ : M ⟶ N) (h : ∀ i, IsIso ((L((a i)^*[ModuleCat.{u + 1} A])).map φ)) :
    IsIso φ := by
  rw [_root_.DerivedCategory.isIso_iff]
  intro n
  refine isIso_of_isIso_upperStar_map_of_jointlySurjective
    (ModuleCat.{u + 1} A) a ha _ fun i ↦ ?_
  have h' : IsIso (D((a i)^*[ModuleCat.{u + 1} A]).map φ) :=
    (NatIso.isIso_map_iff (leftDerivedUpperStarIsoMapDerivedCategory _ _) φ).1 (h i)
  exact (NatIso.isIso_map_iff
    (((a i)^*[ModuleCat.{u + 1} A]).mapDerivedCategoryHomologyFunctorIso n) φ).2
    (Functor.map_isIso (_root_.DerivedCategory.homologyFunctor _ n)
      (D((a i)^*[ModuleCat.{u + 1} A]).map φ))

end AlgebraicGeometry.Etale
