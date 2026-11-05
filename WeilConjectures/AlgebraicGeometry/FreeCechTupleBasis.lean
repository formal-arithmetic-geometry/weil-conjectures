/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.Cech
public import WeilConjectures.AlgebraicGeometry.PowerSetComplexContractible
public import Mathlib.LinearAlgebra.DFinsupp

/-! # Tuple generators of the evaluated free Čech object

Source: Stacks Project, Tags 03AT and 03F5, the degreewise direct-sum decomposition.
(blueprint: lem-weil-pbc-free-cech-tuple-basis)
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite Simplicial

namespace AlgebraicGeometry

variable (X : Scheme.{u}) (ι : Type u) (U₀ : X.Etale) (U : ι → X.Etale)
  (f : ∀ i : ι, U i ⟶ U₀) (O : X.Etaleᵒᵖ ⥤ RingCat.{u}) (W : X.Etale)

/-- Lifts of a fixed map to the base, retaining their family indices.
Source: Stacks Project, Tag 03AT (blueprint: lem-weil-pbc-free-cech-tuple-basis). -/
abbrev freeCechLifts (φ : W ⟶ U₀) := Σ i : ι, {g : W ⟶ U i // g ≫ f i = φ}

end AlgebraicGeometry
