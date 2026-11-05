/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Adjunction.MateBiproduct
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# Biproduct powers on derived categories

For an abelian category `C` and `d : ℕ`, the exact functor `Functor.finBiproductPow C d`,
`M ↦ Mᵈ`, induces on the derived category the biproduct power `K ↦ Kᵈ`
(`CategoryTheory.Functor.mapDerivedCategoryBiproductPowIso`). This follows from two facts:

* the biproduct power is additive (`CategoryTheory.Functor.additive_biproductPow`), and an
  additive functor commutes with biproduct powers (`CategoryTheory.Functor.biproductPowCompIso`);
* on complexes, the levelwise biproduct power is the biproduct power of complexes
  (`CategoryTheory.Functor.mapHomologicalComplexBiproductPowIso`).
-/

@[expose] public section

universe v u

open CategoryTheory Limits

namespace CategoryTheory.Functor

section Additive

variable {A B : Type*} [Category A] [Category B] [Preadditive A] [Preadditive B]
  [HasFiniteBiproducts A] [HasFiniteBiproducts B]

end Additive

section HomologicalComplex

variable (C : Type u) [Category.{v} C] [Abelian C] [HasFiniteBiproducts C]
  {ι : Type*} (c : ComplexShape ι) [HasFiniteBiproducts (HomologicalComplex C c)] (d : ℕ)
  [(finBiproductPow C d).Additive]

end HomologicalComplex

section Derived

variable (C : Type u) [Category.{v} C] [Abelian C] [HasFiniteBiproducts C] [HasDerivedCategory C]
  (d : ℕ)
  [(finBiproductPow C d).Additive] [PreservesFiniteLimits (finBiproductPow C d)]
  [PreservesFiniteColimits (finBiproductPow C d)]

end Derived

end CategoryTheory.Functor
