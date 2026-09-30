/-
Copyright (c) 2026 The Weil Conjectures Project Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Mapping cones of bounded below complexes

The mapping cone of a morphism between cochain complexes which are strictly `≥ a` is strictly
`≥ a - 1`.
-/

@[expose] public section

namespace CochainComplex.mappingCone

open CategoryTheory Limits HomologicalComplex

variable {C : Type*} [Category* C] [Preadditive C]
  {K L : CochainComplex C ℤ} (φ : K ⟶ L) [HasHomotopyCofiber φ]

/-- The mapping cone of a morphism `φ : K ⟶ L` between cochain complexes which are strictly
`≥ a` is strictly `≥ a - 1`, since `(mappingCone φ)ⁱ = Kⁱ⁺¹ ⊞ Lⁱ`. -/
lemma isStrictlyGE (a : ℤ) [CochainComplex.IsStrictlyGE K a] [CochainComplex.IsStrictlyGE L a] :
    (mappingCone φ).IsStrictlyGE (a - 1) := by
  rw [isStrictlyGE_iff]
  intro i hi
  rw [isZero_X_iff]
  exact ⟨K.isZero_of_isStrictlyGE a _, L.isZero_of_isStrictlyGE a _⟩

end CochainComplex.mappingCone
