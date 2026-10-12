/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group M1
-/
module

import Sheaf.AlgebraicGeometry.CoherentFormalModulesAffine
import Sheaf.AlgebraicGeometry.CoherentFormalModulesAbelian
public import Mathlib.Algebra.Category.ModuleCat.Limits
public import Mathlib.Data.List.TFAE
public import Mathlib.RingTheory.Ideal.Operations
import Sheaf.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
public import Sheaf.AlgebraicGeometry.CoherentFormalModule
import Sheaf.AlgebraicGeometry.CoherentFormalModulesLocalExactness
import Sheaf.AlgebraicGeometry.Modules.IdealTimesQuasiCoherentAffineSections
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.RingTheory.AdicCompletionNoetherian
import Sheaf.RingTheory.KernelCokernelAnnihilatedModIdeal
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel

/-! # Annihilation of kernels and cokernels of coherent formal module maps -/

@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- An intermediate kernel-annihilation component of the affine-cover reduction.
Source: Stacks, Remark 0888 (blueprint: lem-weil-pbc-formal-systems-annihilated-by-power-kernel).
The proof is the corresponding kernel/cokernel half of the finite affine-cover
argument. The finite affine cover is reduced modulo each power of the ideal, the
commutative-algebra annihilation lemma is applied, and local annihilation is glued
over the affine cover.
-/
theorem coherentFormalModule_annihilated_double_kernel (X : Scheme.{u}) [IsNoetherian X]
    (I K : X.IdealSheafData) (F G : CoherentFormalModule X I) (α : F ⟶ G)
    (r : ℕ) (U : Fin r → X.affineOpens) (t : ℕ)
    (hcover : (⨆ i, (U i).1) = ⊤) (ht : 1 ≤ t)
    (h : ∀ i : Fin r,
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1) (LinearMap.ker
        (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom) ∧
      K.ideal (U i) ^ t ≤ Module.annihilator Γ(X, (U i).1)
        (↥(limit (G.obj ⋙
          SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)) :
          ModuleCat Γ(X, (U i).1)) ⧸ LinearMap.range
          (lim.map (Functor.whiskerRight α.hom
          (SheafOfModules.evaluation X.ringCatSheaf (op (U i).1)))).hom)) :
    ∀ n : ℕ,
      IsZero (Scheme.idealModuleProduct (Scheme.idealSheafPower K.toModulesι (2 * t)).2
        (kernel (α.hom.app (op n)))) := by
  sorry

end AlgebraicGeometry
