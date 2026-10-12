/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M2
-/
module

public import Sheaf.AlgebraicGeometry.PositiveTensorFamily
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Sheaf.AlgebraicGeometry.TensorGeneratingSections

/-! # Tensor generation with arbitrary finite index types

Source: Stacks Project, Modules, Tag 01AO.
-/

@[expose] public section

universe v

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry.Scheme.Modules

/-- Finite generating families indexed by arbitrary finite types generate the positive
iterated tensor product through their pure tensors.
Source: Stacks Project, Modules, Tag 01AO (blueprint: lem-sc-finite-tensor-generating-sections).

Proof: when every index type is nonempty, choose equivalences to finite ordinal index types
and lift them to the universe of the sheaf. Apply `tensor_generating_sections` after these
reindexings. The product of the equivalences reindexes the tuple family, and the induced
free-sheaf isomorphism preserves epimorphisms. If a factor's index type is empty, its free
sheaf is zero and its epimorphic generating map forces that factor to be zero. Tensoring
with zero gives zero; hence both the tensor product and its empty tuple-indexed free sheaf
are zero, and the displayed map is an epimorphism. -/
theorem finite_tensor_generating_sections {X : Scheme.{v}}
    (n : ℕ) (L : Fin (n + 1) → X.Modules)
    (σ : (i : Fin (n + 1)) → SheafOfModules.GeneratingSections (L i))
    (hσ : ∀ i, (σ i).IsFiniteType) :
    Epi ((positiveTensorFamily n L).freeHomEquiv.symm
      (fun j : (i : Fin (n + 1)) → (σ i).I ↦
        positiveTensorFamilySection n L (fun i ↦ (σ i).s (j i)))) := by
  sorry

end AlgebraicGeometry.Scheme.Modules
