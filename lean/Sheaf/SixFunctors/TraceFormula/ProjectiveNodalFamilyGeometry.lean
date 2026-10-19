/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q71
-/
module

public import Sheaf.AlgebraicGeometry.NodalGeometricFibres
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.AlgebraicGeometry.Morphisms.Projective
import Mathlib.AlgebraicGeometry.Fiber
import Sheaf.AlgebraicGeometry.Morphisms.ProjectiveBaseChange
import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.Curve.SmoothProjective
import Sheaf.AlgebraicGeometry.ZeroDimensionalClosedSubschemeFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.UnramifiedBaseChangeOpen
import WeilConjectures.AlgebraicGeometry.UnramifiedOverFieldDiscrete
import Sheaf.AlgebraicGeometry.FirstFittingSingularSubscheme
import Sheaf.SixFunctors.TraceFormula.NodalFamilyFittingSingular

/-! # Base change and the unramified singular subscheme of a nodal family

Source: Stacks Project, Tags 0C59 and 0C5B (blueprint:
`lem-trf-projective-nodal-family-geometry`).

## Main statement

* `projective_nodal_family_geometry`: the smooth locus of a projective flat nodal
  family is open and its canonical singular closed subscheme is unramified with
  finite fibres, with the stated base-change properties.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- The canonical map `S ×_Y Y₁ ⟶ X ×_Y Y₁` induced by `i : S ⟶ X`.
Source: Stacks Tag 0C5B, base change of the singular closed subscheme
(blueprint: lem-trf-projective-nodal-family-geometry). -/
noncomputable def nodalSingularBaseChangeMap
    {S X Y Y₁ : Scheme.{u}} (f : X ⟶ Y) (i : S ⟶ X) (g : Y₁ ⟶ Y) :
    pullback (i ≫ f) g ⟶ pullback f g :=
  pullback.map (i ≫ f) g f g i (𝟙 Y₁) (𝟙 Y)
    (Category.comp_id (i ≫ f))
    ((Category.comp_id g).trans (Category.id_comp g).symm)

/-- Projective nodal families have an unramified closed singular subscheme with finite
fibres, compatibly with every Noetherian base change.
Source: Stacks Tags 0C59 and 0C5B
(blueprint: lem-trf-projective-nodal-family-geometry).

Proof plan:
1. Apply `lem-trf-nodal-family-fitting-singular` and choose the first-Fitting singular
   subscheme from `def-trf-first-fitting-singular-subscheme`. Its support is the
   nonsmooth locus and its morphism to the base is unramified.
2. On each scheme-theoretic fibre, unramifiedness gives a discrete space. Closed
   immersion and projectivity give a finite-type zero-dimensional closed subscheme;
   `lem-pc-zero-dimensional-closed-subscheme-finite` makes it affine and finite.
   A discrete quasi-compact space is finite, giving the underlying finite fibres.
3. Projectivity, flatness and local finite presentation survive base change by
   `lem-pc-projective-base-change`, `lem-weil-pbc-flat-morphism-base-change` and
   `lem-weil-pbc-qcqs-morphism-permanence`. Geometric fibres agree by pullback pasting.
4. Fitting formation commutes with base change by the nodal-family fitting lemma.
   Its support clause identifies the new nonsmooth locus with the preimage of the
   old one and gives the assertions about the same base-changed singular subscheme.
-/
theorem projective_nodal_family_geometry
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsNoetherian Y] [IsHProjective f] [Flat f]
    [LocallyOfFinitePresentation f] (hN : HasNodalGeometricFibres f) :
    IsOpen (f.smoothLocus : Set X) ∧
      ∃ (S : Scheme.{u}) (i : S ⟶ X),
        IsClosedImmersion i ∧
        (LocallyOfFiniteType (i ≫ f) ∧ IsOpenImmersion (pullback.diagonal (i ≫ f))) ∧
        Set.range i = (f.smoothLocus : Set X)ᶜ ∧
        (∀ y : Y, Set.Finite ((i ≫ f) ⁻¹' {y})) ∧
        ∀ (Y₁ : Scheme.{u}) (g : Y₁ ⟶ Y) [IsNoetherian Y₁],
          IsHProjective (pullback.snd f g) ∧ Flat (pullback.snd f g) ∧
          LocallyOfFinitePresentation (pullback.snd f g) ∧
          HasNodalGeometricFibres (pullback.snd f g) ∧
          (pullback.fst f g) ⁻¹ᵁ f.smoothLocus = (pullback.snd f g).smoothLocus ∧
          IsClosedImmersion (nodalSingularBaseChangeMap f i g) ∧
          (LocallyOfFiniteType (pullback.snd (i ≫ f) g) ∧
            IsOpenImmersion (pullback.diagonal (pullback.snd (i ≫ f) g))) ∧
          Set.range (nodalSingularBaseChangeMap f i g) =
            ((pullback.snd f g).smoothLocus : Set (pullback f g : Scheme.{u}))ᶜ := by
  sorry

end AlgebraicGeometry
