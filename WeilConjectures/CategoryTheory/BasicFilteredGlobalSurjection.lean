/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.CanonicalFiltration
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Ring.Defs
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Quotient.Basic

/-! The explicit basic complex `P₀` and its map `f₀` of Stacks Tag 0H7X.
Global and filtered cocycles index a free zero-differential complex, with the filtration
spanned by the filtered generators whose step index is at least the filtration index.
(blueprint: lem-pur-kunneth-basic-filtered-surjection-global)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open Module
namespace CategoryTheory

abbrev P0Cycle (R : Type u) [CommRing R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (n : ℤ) :=
  {z : K.obj.X n // K.obj.d n (n + 1) z = 0}

abbrev P0StepCycle (R : Type u) [CommRing R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ))
    (j n : ℤ) :=
  {z : K.obj.X n // (∃ x : (K.filtration.step j : CochainComplex (ModuleCat.{u} R) ℤ).X n,
      (K.filtration.step j).arrow.f n x = z) ∧ K.obj.d n (n + 1) z = 0}

abbrev P0Index (R : Type u) [CommRing R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ)) (n : ℤ) :=
  P0Cycle R K n ⊕ (Σ j : ℤ, P0StepCycle R K j n)

noncomputable def P0Index.map (R : Type u) [CommRing R]
    (K : FilteredObject (CochainComplex (ModuleCat.{u} R) ℤ))
    (n : ℤ) : P0Index R K n → K.obj.X n := fun z =>
  match z with
  | Sum.inl z => z.1
  | Sum.inr z => z.2.1
end CategoryTheory
