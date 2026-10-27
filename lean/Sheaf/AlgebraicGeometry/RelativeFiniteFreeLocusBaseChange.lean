/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q29
-/
module

public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Sheaf.AlgebraicGeometry.CoherentFiniteType
public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Sheaf.AlgebraicGeometry.TensorPullbackSectionAdjunction

import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
import WeilConjectures.AlgebraicGeometry.FinitePresentationSourceStalk
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Flat.Basic
import Mathlib.RingTheory.LocalRing.Module

/-! # Relative finite locally free loci and arbitrary base change

Source: Stacks Project, More on Morphisms, Tag 0CZR, `lemma-finite-free-open`
(blueprint: lem-sfb-relative-finite-free-locus-base-change).

The locus uses actual finite free trivializations on Zariski open neighbourhoods.
The sheaf is flat over the base; the structural morphism need not be flat.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

/-- Points admitting a Zariski open neighbourhood with a finite free trivialization.
`ULift` puts the finite index type in the section universe, and rank zero is allowed.
Source: Stacks Project, More on Morphisms, Tag 0CZR, the displayed locus
(blueprint: lem-sfb-relative-finite-free-locus-base-change). -/
def finiteFreeLocus {Y : Scheme.{u}} (F : Y.Modules) : Set Y :=
  {y | ∃ U : Y.Opens, y ∈ U ∧ ∃ r : ℕ,
    Nonempty (F.over U ≅
      SheafOfModules.free (R := Y.ringCatSheaf.over U) (ULift.{u} (Fin r)))}

/-- The finite free locus is open and commutes with arbitrary change of the scheme base.
Source: Stacks Project, More on Morphisms, Tag 0CZR, statement and proof
(blueprint: lem-sfb-relative-finite-free-locus-base-change).

Proof:
1. The locus is the union of the open neighbourhoods carrying finite free trivializations,
   so it is open.
2. Identify it with the locus of points where the stalk is flat over the local ring of Y.
   A finite free stalk is flat by `lem-sc-affine-standard-cover-finite-free-local-fp-flat`.
   Conversely `lem-weil-pbc-finite-presentation-source-stalk` makes the stalk finitely
   presented, hence finite. It is free by `lem-weil-pbc-finite-flat-local-free`.
   A finite generating family uses finitely many basis vectors; these contain every
   basis vector, so the basis is finite. Spread it with
   `lem-trf-finite-presentation-stalk-basis-spread`. The empty basis covers the zero stalk.
3. Apply `lem-sfb-relative-module-flat-locus-base-change` to the identity of Y over T.
   The structural morphism is locally of finite type by
   `lem-a1-map-over-base-finite-presentation`, applied to p and the identity of T.
   The resulting equality of total stalk-flat loci applies to every v, and only requires
   the relative flatness of F, not flatness of p.
4. A point in the finite free locus of the pullback has a flat stalk; step 3 followed by
   step 2 places its image in the original finite free locus. For the reverse inclusion,
   pull a trivialization back to the inverse image open. Tensor coordinates identify
   a tensor (b_i) with (a*b_i); the inverse sends (c_i) to the sum of c_i tensor e_i.
   This is compatible with restrictions and gives the required finite free trivialization.
-/
theorem relative_finiteFreeLocus_baseChange {Y T : Scheme.{u}} (p : Y ⟶ T)
    [LocallyOfFinitePresentation p] (F : Y.Modules)
    [SheafOfModules.IsFinitePresentation.{u} F] (hflat : F.IsFlatOver p) :
    IsOpen (finiteFreeLocus F) ∧
      ∀ (T₁ : Scheme.{u}) (v : T₁ ⟶ T),
        finiteFreeLocus ((tensorPullback (pullback.fst p v)).obj F) =
          (pullback.fst p v) ⁻¹' finiteFreeLocus F := by
  sorry

end AlgebraicGeometry.Scheme.Modules
