/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Q13
-/
module

public import Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceQuasiCoherentModule
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceModuleOperations
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers
public import Sheaf.AlgebraicGeometry.AlgebraicSpaceFlatProperCoefficient
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

import Sheaf.AlgebraicGeometry.AlgebraicSpaceAffineEtaleCover
import Sheaf.AlgebraicGeometry.AlgebraicSpaceModulePullbackQuasiCoherent
import Sheaf.AlgebraicGeometry.SpaceFinitePresentationModuleLimit
import Mathlib.RingTheory.FiniteStability
import Mathlib.RingTheory.FinitePresentation

/-! # Relative finite locally free loci and arbitrary base change

Source: Stacks Project, More on Morphisms of Spaces, Tag 0CZT (lemma-finite-free-open)
(blueprint: lem-sfb-space-relative-finite-free-locus-base-change).

The locus is defined by actual finite free trivializations on small étale slices.
The base-change assertion uses a pullback square, so it applies to every realization
of the fibre product with its specified projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.AlgebraicSpace

/-- Points admitting an étale neighbourhood with a finite free trivialization.
The rank may be zero; `ULift` places the finite basis in the section universe.
Source: Stacks Project, More on Morphisms of Spaces, Tag 0CZT, the displayed locus
(blueprint: lem-sfb-space-relative-finite-free-locus-base-change). -/
def finiteFreeLocus {S : Scheme.{u}} (X : AlgebraicSpace S) (F : X.Modules) :
    Set (Point X.obj.obj) :=
  {x | ∃ U : X.EtaleSite, x ∈ pointImage U.obj.hom ∧
    ∃ r : ℕ, Nonempty ((X.etalePullback U).obj F ≅
      SheafOfModules.free (R := X.structureSheaf.over U) (ULift.{u} (Fin r)))}

/-- The finite locally free locus of a finitely presented module flat over the base
is open and commutes with arbitrary base change when the structural map is locally
finitely presented.
Source: Stacks Project, More on Morphisms of Spaces, Tag 0CZT, statement and proof
(blueprint: lem-sfb-space-relative-finite-free-locus-base-change).

Proof: (1) Each trivializing étale chart has open point image, by
`lem-a1-space-affine-etale-cover`; the locus is the union of these images.
(2) Local finite presentation of the morphism survives base change, using
`lem-sfb-space-local-properties-chart-test`,
`lem-trf-space-fibre-products-etale-covers`, and
`lem-weil-pbc-finite-presentation-base-change-composition` on scheme charts.
The pullback module is quasi-coherent by `lem-sfb-space-module-pullback-quasicoherent`,
finitely presented by the pullback clause of `lem-sfb-space-fp-module-limit-category`,
and relatively flat by `lem-sfb-space-pointwise-module-flat-base-change`.
(3) Represent a point of the pullback by Spec K. Its fibre over the induced K-point
of the new base is canonically the fibre of X over the composite K-point of Y:
((a,b),c) maps to (a,c), with inverse (a,c) mapping to ((a,eta' c),c).
These inverse maps identify the tautological points. Tensor reassociation identifies
the two fibre modules, using `def-trf-space-etale-module-functors`.
(4) Apply `lem-sfb-space-fibre-flat-free-criterion` to both modules. Membership in
each finite free locus is flatness of the corresponding fibre module at that point;
step (3) identifies the two conditions. This proves equality of the two subsets,
including the rank-zero case, without any flatness assumption on either base map. -/
theorem relativeFiniteFreeLocus_baseChange {S : Scheme.{u}} {X Y : AlgebraicSpace S}
    (p : X ⟶ Y) (hp : MapIsLocallyOfFinitePresentation p) (F : X.QCoh)
    (hF : SheafOfModules.IsFinitePresentation F.obj) (hflat : ModuleIsFlatOver p F.obj) :
    IsOpen (finiteFreeLocus X F.obj) ∧
      ∀ (Y' : AlgebraicSpace S) (v : Y' ⟶ Y) (X' : AlgebraicSpace S)
        (q : X' ⟶ X) (p' : X' ⟶ Y'), IsPullback q p' p v →
        finiteFreeLocus X' ((moduleTensorPullback q).obj F.obj) =
          (mapPoint q.hom.hom) ⁻¹' finiteFreeLocus X F.obj := by
  sorry

end AlgebraicGeometry.AlgebraicSpace
