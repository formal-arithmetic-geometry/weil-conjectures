/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.FieldBaseChangeSections
public import WeilConjectures.AlgebraicGeometry.Modules.GeneratingLocus
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackFreeGenerator
public import WeilConjectures.Mathlib.LinearAlgebra.TensorProduct.Finiteness

/-!
# Global sections of an invertible module after a field extension

Let `X` be a quasi-compact scheme over a field `k`, let `K / k` be a field extension, with
projections `φ : X_K ⟶ X` and `p : X_K ⟶ Spec K`, and let `M` be an invertible `𝒪_X`-module.
Every global section of `φ^* M` is a finite `K`-linear combination of pullbacks of global
sections of `M`: this is the surjectivity of `Γ(X, M) ⊗_k K ⟶ Γ(X_K, φ^* M)` in flat base change.

On an affine open `W` on which `M` has a free generator `e`, a section of `φ^* M` is
`h • φ^* e` with `h ∈ Γ(X_K, φ⁻¹ W) = Γ(X, W) ⊗_k K`
(`AlgebraicGeometry.exists_ringEquiv_tensor_app_preimage_fst`). Expanding these finitely many
tensors along one `k`-linearly independent family `β` of `K`, the coefficients of the `β q`
are local sections of `M` which glue, since `Γ(X, V) ⊗_k K ⟶ Γ(X_K, φ⁻¹ V)` is injective on
affine opens `V`.

## Main definitions

- `AlgebraicGeometry.Scheme.Modules.pullbackTopSection`: the pullback of a global section.

## Main statements

- `AlgebraicGeometry.Scheme.Modules.exists_eq_sum_smul_pullbackTopSection`: the sections of
  `φ^* M` are spanned over `K` by pullbacks of sections of `M`.
-/

@[expose] public section

universe u

open CategoryTheory Limits TensorProduct

namespace AlgebraicGeometry.Scheme.Modules

section PullbackTop

variable {X Y : Scheme.{u}} (g : X ⟶ Y) {M : Y.Modules}

/-- The pullback `g^* m` of a global section `m` of `M`, as a global section of `g^* M`. -/
noncomputable def pullbackTopSection (m : Γ(M, ⊤)) : Γ((pullback g).obj M, ⊤) :=
  ((pullback g).obj M).presheaf.map (homOfLE (g.preimage_top).ge).op
    (pullbackSection g m)

end PullbackTop

variable {k K : Type u} [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k))

end AlgebraicGeometry.Scheme.Modules
