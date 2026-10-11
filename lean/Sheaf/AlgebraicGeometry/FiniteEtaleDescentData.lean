/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Sheaf.AlgebraicGeometry.FpqcSingletonFullyFaithful
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Finite etale descent data

Source: Stacks Project, Descent, Definition 35.34.1 (Tag 023V), and the
finite-etale specialization in the blueprint's `lem-galois-descent`
(blueprint: def-galois-finite-etale-descent-data).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The category of finite etale schemes over `Y'` equipped with descent data
relative to `g : Y' ⟶ Y`. Morphisms are all morphisms over `Y'` compatible
with the data, as in Stacks Project, Descent, Tag 023V
(blueprint: def-galois-finite-etale-descent-data). -/
protected abbrev FiniteEtaleDescentData {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) :
    Type (u + 1) :=
  ObjectProperty.FullSubcategory fun A : Over.DescentDataCategory g ↦
    IsFinite A.V.hom ∧ Etale A.V.hom

end AlgebraicGeometry
