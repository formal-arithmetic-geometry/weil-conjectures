/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.Specialization.TraitSliceGaloisTensor

/-!

# The residue field of `Ω ⊗_{k'((t))} K((t))` and the compositum `K((t))·Ω ⊆ Ω_K`

Let `F = k'((t))`, `F_K = K((t))`, `Ω = F^alg`, `Ω_K = F_K^alg` and `F^sep ⊆ Ω` the separable
closure. The product map `Ω ⊗_F F_K ⟶ Ω_K` (`AlgebraicGeometry.traitGenericTensorLift`, from the
embedding `Ω ⟶ Ω_K` over `F ⟶ F_K`) has image the compositum `L = F_K·Ω`
(`AlgebraicGeometry.traitGenericCompositum`, `AlgebraicGeometry.range_traitGenericTensorLift`).
Since `Spec(Ω ⊗_F F_K)` is a single point
(`AlgebraicGeometry.subsingleton_primeSpectrum_traitGenericField_tensorProduct`), its kernel is
the nilradical (`AlgebraicGeometry.ker_traitGenericTensorLift`), so `L` is the residue field of
the unique point (`AlgebraicGeometry.traitGenericTensorResidueEquiv`). Moreover:

* `L` is purely inseparable over `F_K·F^sep`
  (`AlgebraicGeometry.isPurelyInseparable_traitGenericCompositum`);
* `Ω_K / L` is algebraic, `L^sep / L` is Galois and `Ω_K / L^sep` is purely inseparable
  (`AlgebraicGeometry.traitGenericCompositum_tower`).

-/

@[expose] public section

open IntermediateField

open scoped TensorProduct

universe u

namespace AlgebraicGeometry

variable (k' : Type u) [Field k'] (K : Type u) [Field K] [Algebra k' K]

variable {k' K} [IsSepClosed k'] [IsAlgClosed K]

end AlgebraicGeometry
