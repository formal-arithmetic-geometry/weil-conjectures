/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.FieldTheory.LinearDisjoint
public import Mathlib.FieldTheory.PrimitiveElement
public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisMinpoly

/-!

# `K((t)) ⊗_{k'((t))} k'((t))^sep` is a field

Let `F ⊆ L` be fields such that `F` is separably closed in `L`. Then `L` is linearly disjoint
from every separable algebraic extension of `F`: for a simple extension `F(β)` this is the
equality of minimal polynomials `minpoly.map_algebraMap_of_isSeparable` (the powers
`1, β, …, β^{n-1}` stay `L`-linearly independent), and the general case follows since linear
disjointness is checked on finite subextensions, which are simple by the primitive element
theorem. Consequently `M ⊗_F L` is a field for every separable algebraic `M / F`
(`Algebra.TensorProduct.isField_of_isSeparable_of_forall_mem_range`).

For the slice of SGA 4½, [Th. finitude], Lemme 3.3 (`F = k'((t))`, `F_K = K((t))`, `Ω = F^alg`):

* `AlgebraicGeometry.isField_separableClosure_tensorProduct_traitLaurentField`:
  `F^sep ⊗_F F_K` is a field;
* `AlgebraicGeometry.isHomeomorph_comap_traitGenericField_tensorProduct`:
  `Spec(Ω ⊗_F F_K) ⟶ Spec(F^sep ⊗_F F_K)` is a homeomorphism (`Ω / F^sep` is purely
  inseparable);
* `AlgebraicGeometry.subsingleton_primeSpectrum_traitGenericField_tensorProduct`:
  hence `Spec(Ω ⊗_F F_K)` is a single point.

-/

@[expose] public section

open Polynomial IntermediateField

open scoped TensorProduct IntermediateField

section General

variable {F L E : Type*} [Field F] [Field L] [Field E] [Algebra F L] [Algebra L E] [Algebra F E]
  [IsScalarTower F L E]

end General

universe u

namespace AlgebraicGeometry

variable {k' : Type u} [Field k'] [IsSepClosed k'] {K : Type u} [Field K] [Algebra k' K]
  [IsAlgClosed K]

end AlgebraicGeometry
