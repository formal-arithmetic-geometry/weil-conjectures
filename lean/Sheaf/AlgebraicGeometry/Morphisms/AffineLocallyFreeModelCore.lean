/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Stalk
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
@[expose] public section
universe u
open CategoryTheory Opposite TopCat.Presheaf
namespace AlgebraicGeometry.Scheme
/-- Finite locally free data extends across an affine open with finite affine sections.
Source: Stacks Project, Tags 0G41(2), 0EY6. (blueprint: new-affine-locally-free-model-core)
The extension theorem is obtained by finite-presentation extension and affine
identification; the restriction isomorphism is transported across the
finite locally free module on the open. -/
theorem exists_affine_locally_free_model_core
    (A : CommRingCat.{u}) [IsNoetherianRing A] (W : (Spec A).Opens)
    (P : W.toScheme.Modules) [P.IsFiniteLocallyFree] :
    ∃ H : (Spec A).Modules,
      H.IsQuasicoherent ∧
      (∀ V : (Spec A).Opens, IsAffineOpen V →
        Module.Finite ((Spec A).presheaf.obj (op V)) (H.val.obj (op V))) ∧
      Nonempty (Modules.restrict H W.ι ≅ P) := by sorry
end AlgebraicGeometry.Scheme
