/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.FirstFittingSingularSubscheme
public import WeilConjectures.AlgebraicGeometry.PureDimension
public import WeilConjectures.AlgebraicGeometry.ProjectiveNodalTower
import WeilConjectures.AlgebraicGeometry.GeometricFibreUnramifiedCriterion
import WeilConjectures.AlgebraicGeometry.DthFittingSmoothLocus
import WeilConjectures.AlgebraicGeometry.NodalCurveLCICriterion
import WeilConjectures.AlgebraicGeometry.UnramifiedMorphism

/-!
# Fitting singular subscheme of a nodal relative curve

Source: Stacks Project, Curves, Tags 0C59 and 0C5B, with Divisors Tags 0C3I,
0C3J and 0C3K (blueprint: lem-trf-nodal-family-fitting-singular).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The first-Fitting singular subscheme of a flat locally finitely presented nodal
relative curve is the nonsmooth locus, is unramified over the base, and commutes
canonically with arbitrary base change.

Source: Stacks Project, Curves, Tags 0C59 and 0C5B, with Divisors Tags 0C3I,
0C3J and 0C3K (blueprint: lem-trf-nodal-family-fitting-singular).

Proof plan:
1. On affine charts, Kähler differentials commute with base change and the defining
   minors of the first Fitting ideal commute with tensor product, so the singular
   closed subscheme base changes canonically.
2. Apply the d-th Fitting smooth-locus criterion with d = 1 to identify the support
   with the complement of the relative smooth locus.
3. On geometric fibres, the nodal curve criterion makes the singular fibre
   unramified; the geometric-fibre unramified criterion then gives unramifiedness
   over the base.
4. Repeat the smooth-locus argument after arbitrary base change and combine it with
   the canonical base-change isomorphism.
-/
theorem nodal_family_fitting_singular
    {X S : Scheme.{u}} (f : X ⟶ S) [Flat f] [LocallyOfFinitePresentation f]
    (hgeom : ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (g : Spec (.of Ω) ⟶ S),
      Nonempty (pullback (C := Scheme.{u}) f g) →
        (pullback (C := Scheme.{u}) f g).IsPureDimension 1 ∧
          ∀ x : pullback (C := Scheme.{u}) f g,
            x ∉ (pullback.snd f g).smoothLocus →
              IsGeometricOrdinaryDoublePoint Ω (pullback (C := Scheme.{u}) f g) x) :
    IsOpen (f.smoothLocus : Set X) ∧
      Set.range (Scheme.firstFittingSingularSubscheme f) = (f.smoothLocus : Set X)ᶜ ∧
      (LocallyOfFiniteType (Scheme.firstFittingSingularSubscheme f ≫ f) ∧
        IsOpenImmersion (pullback.diagonal (Scheme.firstFittingSingularSubscheme f ≫ f))) ∧
      ∀ (S' : Scheme.{u}) (g : S' ⟶ S),
        Nonempty
            (Over.mk
                (pullback.map (Scheme.firstFittingSingularSubscheme f ≫ f) g f g
                  (Scheme.firstFittingSingularSubscheme f) (𝟙 S') (𝟙 S)
                  (Category.comp_id (Scheme.firstFittingSingularSubscheme f ≫ f))
                  ((Category.comp_id g).trans (Category.id_comp g).symm)) ≅
              Over.mk (Scheme.firstFittingSingularSubscheme (pullback.snd f g))) ∧
          Set.range (Scheme.firstFittingSingularSubscheme (pullback.snd f g)) =
            ((pullback.snd f g).smoothLocus : Set (pullback (C := Scheme.{u}) f g))ᶜ := by
  sorry

end AlgebraicGeometry
