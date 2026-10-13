/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R4
-/
module

public import Sheaf.Paper.DerivedHomMayerVietoris
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-! # Exactness of complexes of module sheaves on a union of opens

Source: Stacks Project, Modules, Tag 01AG.
(blueprint: lem-r4-open-cover-restriction-exact).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry

/-- Exactness of a complex after open restriction is local on an open cover.
Source: Stacks Project, Modules, Tag 01AG (lemma-abelian), applied to the
short complex of consecutive differentials in a fixed degree.
(blueprint: lem-r4-open-cover-restriction-exact).

Proof: Fix a point x of U and choose an index i with x in V_i using hU.
Restriction to an open containing x does not change stalks. The exactness
hypothesis on V_i therefore gives exactness of the original complex at
its stalk at x in degree n. This holds for every x of U. The stalkwise
exactness criterion for module sheaves gives exactness of the restricted
short complex of consecutive differentials, hence ExactAt n. Equivalently,
a section killed by the outgoing differential admits local lifts on the
cover and thus near every point of its domain. This is sheaf exactness,
not surjectivity on global sections. The same proof includes the empty
cover: U is then empty and every module sheaf over U is zero. -/
theorem exactAt_over_of_open_cover
    (X : Scheme.{u}) (K : CochainComplex
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (ι : Type v) (V : ι → X.Opens) (U : X.Opens) (hU : U = ⨆ i, V i)
    (n : ℤ)
    (h : ∀ i, (((SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) (V i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K).ExactAt n) :
    (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).ExactAt n := by sorry

end AlgebraicGeometry
