/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.ConstructibleSheaf.Defs
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheafOver
import WeilConjectures.ConstructibleSheaf.ConstantFiniteFreeDualNaturality

/-!
# Kernels of duals of constant finite free matrices

For a linear map `g : Λ^m → Λ^n`, the kernel of the map induced by `g` on the duals
`[Λ_X^n, Λ_X] ⟶ [Λ_X^m, Λ_X]` is the constant sheaf on the kernel of the dual map of `g`
(`AlgebraicGeometry.Scheme.constantFiniteMatrixDualKernelIso_aux`).

## Implementation details

The kernel on the right is the categorical kernel in `ModuleCat`; its identification with
`LinearMap.ker` via `ModuleCat.kernelIsoKer` is left to the caller.
-/

@[expose] public section
universe u
open CategoryTheory MonoidalCategory Limits
namespace AlgebraicGeometry.Scheme

/-- The finite-free kernel comparison, with the categorical module kernel: the kernel of the
dual of the constant map `Λ_X^m ⟶ Λ_X^n` induced by `g` is the constant sheaf on the kernel of
the dual map of `g`. -/
theorem constantFiniteMatrixDualKernelIso_aux
    (X : Scheme.{u}) {Λ : Type (u + 1)} [CommRing Λ]
    (n m : ℕ) (g : (Fin m → Λ) →ₗ[Λ] (Fin n → Λ)) :
    Nonempty (kernel
      ((MonoidalClosed.internalHom.flip.obj
        (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))).map
          ((constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).map
            (ModuleCat.ofHom g)).op) ≅
      (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)).obj
        (kernel (ModuleCat.ofHom g.dualMap))) := by
  obtain ⟨e, he⟩ := constantFiniteFreeDualNaturality X (Λ := Λ)
  let C := constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)
  let D := MonoidalClosed.internalHom.flip.obj
    (𝟙_ (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  exact ⟨kernel.mapIso (D.map (C.map (ModuleCat.ofHom g)).op)
    (C.map (ModuleCat.ofHom g.dualMap)) (e n) (e m) (he n m g) ≪≫
      (PreservesKernel.iso C (ModuleCat.ofHom g.dualMap)).symm⟩

end AlgebraicGeometry.Scheme
