/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Constructible
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.Extension
public import WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.UnitMatrix
public import WeilConjectures.Mathlib.Topology.Constructible
public import WeilConjectures.Mathlib.CategoryTheory.NatIso
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme

/-!
# Kernels and cokernels of constructible `Λ`-adic sheaves

This is the counterpart, for a coefficient field `Λ` with an ultrametric norm (the case of
interest being a finite extension `E` of `ℚ_ℓ` inside `ℚ̄_ℓ`), of
`WeilConjectures.SixFunctors.ProEtale.Adic.Abelian`, which treats `ℚ̄_ℓ`,
with the same proofs; the constant sheaf `Λ_X : U ↦ C(U, Λ)` is that of
`WeilConjectures.SixFunctors.ProEtale.FieldCoefficient.ConstantSheaf`.

A morphism `ψ : Λ_Tⁿ ⟶ Λ_Tᵐ` of finite free modules is a matrix of continuous
functions on `T` (`AlgebraicGeometry.ProEtale.FieldSheaf.unitMatrix`), and has a rank at every
point of `T`. If this rank is constant, then locally on `T` the morphism is equivalent to
`[[1, 0], [0, 0]]`, so its kernel and cokernel are lisse
(`AlgebraicGeometry.ProEtale.FieldSheaf.isFieldLisseSheaf_kernel_cokernel_of_rank_eq`).

For a morphism `φ` of lisse sheaves on `Y`, the rank of `φ` at a point does not depend on the
trivialisation used to compute it
(`AlgebraicGeometry.ProEtale.FieldSheaf.rank_eq_of_apply_eq`), is lower semicontinuous, and
descends to `Y` along the pro-étale cover
(`AlgebraicGeometry.Scheme.isOpen_of_isOpen_preimage_of_mem_proetalePrecoverage`). On the open
subscheme where it is maximal the kernel and cokernel of `φ` are lisse
(`AlgebraicGeometry.ProEtale.exists_nonempty_isFieldLisseSheaf_kernel_cokernel`), and Noetherian
induction gives finite stratifications on which they are lisse
(`AlgebraicGeometry.ProEtale.IsFieldLisseSheaf.isFieldStratifiedLisseSheaf_kernel_cokernel`).

Refining stratifications, kernels and cokernels of constructible sheaves on a locally Noetherian
scheme are constructible (`AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.kernel_cokernel`).
The Noetherian hypothesis is necessary: if the underlying space of `X` is a profinite set without
isolated points, such as `ℤ_ℓ`, multiplication by the continuous function `t ↦ t` on `Λ_X` has
a cokernel supported at a single non-constructible point.

## Main results

- `AlgebraicGeometry.ProEtale.IsFieldConstructibleSheaf.kernel_cokernel`, and the instances
  `(fieldConstructibleSheaf Λ X).IsClosedUnderKernels` and
  `(fieldConstructibleSheaf Λ X).IsClosedUnderCokernels` for `[IsLocallyNoetherian X]`.
-/

@[expose] public section

open CategoryTheory Limits

namespace AlgebraicGeometry

variable {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ] {T : Type*} [TopologicalSpace T]
  {κ ι : Type*} [Fintype κ]
  [Fintype ι]

end AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProEtale

variable {Λ : Type} [NormedField Λ] [IsUltrametricDist Λ] {T : Scheme.{u}}

attribute [local instance] Abelian.hasFiniteBiproducts

namespace FieldSheaf

variable {ι κ : Type} [Fintype ι] [Fintype κ]

section Rank

variable {P : Scheme.{u}} {ι κ ι' κ' : Type} [Fintype ι] [Fintype κ] [Fintype ι'] [Fintype κ']

section Transport

variable {Y V : Scheme.{u}} {n : ℕ}

end Transport

section Descent

variable {Y V V' : Scheme.{u}} {F G : FieldSheaf Λ Y} (φ : F ⟶ G) {n m n' m' : ℕ}

end Descent

end Rank

end FieldSheaf

section Generic

attribute [local instance] Abelian.hasFiniteBiproducts

end Generic

section Stratification

open TopologicalSpace Topology

end Stratification

section Constructible

open TopologicalSpace Topology

variable {X : Scheme.{u}} [IsLocallyNoetherian X]

end Constructible

end AlgebraicGeometry.ProEtale
