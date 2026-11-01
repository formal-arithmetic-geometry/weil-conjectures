/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerShriek.SmoothPurityTowerShriekLevels
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityCoefficientTowersAbelian
public import WeilConjectures.AlgebraicGeometry.Semilinear.SemilinearDerivedSections
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.AlgebraicGeometry.OpenImmersion
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Triangulated.Pretriangulated
public import WeilConjectures.Compactification.RefinementCategory
public import WeilConjectures.Algebra.Homology.OpenTensorNormalization.ExactDerivedAdjunctionSupplement

/-! # The open-cover triangle of varying-coefficient towers

Source: latest blueprint, sec-smooth-purity/sk-prop-sp-tower-geometric,
`sk-prop-sp-tower-geometric-gluing.proof.md`, Gluing and Levels paragraphs.
(blueprint: lem-dla1-tower-open-cover-triangle-data).

Index `n : ℕ` denotes the paper's positive coefficient level `n + 1`.
The sequence-site presentation `SpTowerShriek.D` is the ordinary derived category
of strict towers, identified sectionwise with `spCoefficientTowers` by `Base.realization`.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

attribute [local irreducible] CategoryTheory.Functor.mapDerivedCategory
  CategoryTheory.Functor.rightDerivedFunctor HasDerivedCategory.standard

universe u v₀ v₁ v₂ u₀ u₁ u₂

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace AlgebraicGeometry.ProEtale.TowerOpenCover

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
  (b : SpTowerShriek.Base l E) (o : SpTowerShriek.Operations l E b)

/-- The specified exact open restriction followed by extension by zero.
Source: latest blueprint, tower-geometric Gluing paragraph.
(blueprint: lem-dla1-tower-open-cover-triangle-data). -/
abbrev support {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j] :=
  SpTowerShriek.pull l E b (o.geometry j) ⋙ SpTowerShriek.openD l E b (o.openOp j)

end AlgebraicGeometry.ProEtale.TowerOpenCover
