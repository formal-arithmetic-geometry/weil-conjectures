/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import WeilConjectures.Algebra.Homology.FlatComplex
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Mathlib.RingTheory.Flat.Basic

/-!
# Base change of quasi-isomorphisms between complexes of flat modules

For an `A`-algebra `B`, extension of scalars `M ↦ B ⊗[A] M` is an additive functor
`ModuleCat.baseChange A B : ModuleCat A ⥤ ModuleCat B`. It sends a quasi-isomorphism
`φ : K ⟶ L` between complexes of flat modules to a quasi-isomorphism, provided the cycles of the
mapping cone of `φ` are flat in high degrees, for instance when `K` and `L` are bounded above
(`CochainComplex.quasiIso_map_baseChange`): the mapping cone is an acyclic complex of flat modules
whose cycles are all flat, so it stays acyclic after base change.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace ModuleCat

variable (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]

end ModuleCat

namespace CochainComplex

variable {A : Type u} [CommRing A] (B : Type u) [CommRing B] [Algebra A B]

variable {K L : CochainComplex (ModuleCat.{u} A) ℤ} (φ : K ⟶ L)

end CochainComplex
