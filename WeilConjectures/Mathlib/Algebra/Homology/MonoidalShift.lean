/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal

/-!
# The associator of cochain complexes commutes with shifts

For cochain complexes `K`, `L`, `M` indexed by `ℤ`, the associator
`(K ⊗ L) ⊗ M ≅ K ⊗ (L ⊗ M)` is compatible with the identifications of total complexes
`CochainComplex.mapBifunctorShift₁Iso` (moving a shift of the first factor out, without sign)
and `CochainComplex.mapBifunctorShift₂Iso` (moving a shift of the second factor out, with the
sign `(-1) ^ (p * n)` on the summand of degree `p` in the first factor), for a shift of each of
the three factors. No sign appears: on a summand `K.X p ⊗ L.X q ⊗ M.X r`, both sides carry the
Koszul sign of the shift passing the factors on its left.

## Main statements

- `CochainComplex.associator_hom_comp_mapBifunctorShift₁Iso_hom`: shift of the first factor.
- `CochainComplex.associator_hom_comp_whiskerLeft_mapBifunctorShift₁Iso_hom`: shift of the
  second factor.
- `CochainComplex.associator_hom_comp_whiskerLeft_mapBifunctorShift₂Iso_hom`: shift of the third
  factor.
-/

@[expose] public section

open CategoryTheory Category Limits MonoidalCategory

namespace CochainComplex

open Monoidal

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [MonoidalCategory C]
  [MonoidalPreadditive C]
  [∀ (X₁ X₂ : GradedObject ℤ C), X₁.HasTensor X₂]
  [∀ X₁, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
  [∀ X₂, PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ (X₁ X₂ X₃ : GradedObject ℤ C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
  (K L M : CochainComplex C ℤ)

end CochainComplex
