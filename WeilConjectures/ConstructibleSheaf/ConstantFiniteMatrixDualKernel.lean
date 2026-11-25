/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.ConstructibleSheaf.ConstantFiniteMatrixDualKernelAux

/-! # Constant finite matrix dual kernels

For a linear map `g : Λᵐ ⟶ Λⁿ` between finite free modules, the kernel of the sheaf dual of the
constant sheaf map induced by `g` is the constant sheaf at `ker g.dualMap`
(`AlgebraicGeometry.Scheme.nonempty_constantFiniteMatrixDualKernelIso`).

## Implementation details

Constant sheafification preserves finite biproducts and sends `Λ` to the tensor unit, so the
dual of the constant sheaf at a finite free module is the constant sheaf at its module dual,
compatibly with `g`; since constant sheafification preserves finite limits, the kernel is the
constant sheaf at the module kernel. This is the finite free transpose argument used for
`IsFiniteLocallyConstantSheaf.ihom_unit`.
-/

@[expose] public section

universe u
open CategoryTheory MonoidalCategory Limits
namespace AlgebraicGeometry.Scheme

/-- The kernel of the sheaf dual of a finite free matrix is constant with its module kernel:
for `g : Λᵐ ⟶ Λⁿ`, the kernel of `Hom(g_X, Λ_X)` is the constant sheaf at `ker g.dualMap`. -/
theorem nonempty_constantFiniteMatrixDualKernelIso
    (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ]
    (n m : ℕ) (g : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)) :
    Nonempty (kernel
      ((MonoidalClosed.internalHom.flip.obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).map
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            (ModuleCat.ofHom g)).op) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (ModuleCat.of Λ (LinearMap.ker g.dualMap))) := by
  obtain ⟨e⟩ := constantFiniteMatrixDualKernelIso_aux X n m g
  exact ⟨e ≪≫
    (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).mapIso
      (ModuleCat.kernelIsoKer (ModuleCat.ofHom g.dualMap))⟩

end AlgebraicGeometry.Scheme
