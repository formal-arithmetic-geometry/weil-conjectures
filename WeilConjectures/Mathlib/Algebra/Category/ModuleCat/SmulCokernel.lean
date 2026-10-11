/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Kernel and cokernel of the multiplication by a scalar

For a module `M` over a commutative ring `R` and `r : R`, the cokernel of the multiplication
`r • 𝟙 M` is the reduction `M ⊗[R] R ⧸ (r)` and its kernel is the `r`-torsion submodule
`Submodule.torsionBy R M r`. For `r` a nonzerodivisor, the latter is `Tor₁^R(M, R ⧸ (r))`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace ModuleCat

variable {R : Type u} [CommRing R] (M : ModuleCat.{u} R) (r : R)

/-- The range of the multiplication by `r` on `M` is `(r) • M`. -/
lemma range_hom_smul_id : LinearMap.range (r • 𝟙 M).hom = Ideal.span {r} • ⊤ := by
  rw [Submodule.ideal_span_singleton_smul]
  ext x
  simp [Submodule.mem_smul_pointwise_iff_exists, eq_comm]

/-- The cokernel of the multiplication by `r` on `M` is the reduction `M ⊗[R] R ⧸ (r)`. -/
noncomputable def cokernelSmulIdIso :
    cokernel (r • 𝟙 M) ≅ ModuleCat.of R (M ⊗[R] (R ⧸ Ideal.span {r})) :=
  cokernelIsoRangeQuotient (r • 𝟙 M) ≪≫
    (Submodule.quotEquivOfEq _ _ (range_hom_smul_id M r)).toModuleIso ≪≫
    (TensorProduct.tensorQuotEquivQuotSMul M (Ideal.span {r})).symm.toModuleIso

/-- The kernel of the multiplication by `r` on `M` is the `r`-torsion submodule of `M`. -/
noncomputable def kernelSmulIdIso :
    kernel (r • 𝟙 M) ≅ ModuleCat.of R (Submodule.torsionBy R M r) :=
  kernelIsoKer (r • 𝟙 M) ≪≫ (LinearEquiv.ofEq _ _ (by
    ext x
    simp [Submodule.mem_torsionBy_iff])).toModuleIso

end ModuleCat
