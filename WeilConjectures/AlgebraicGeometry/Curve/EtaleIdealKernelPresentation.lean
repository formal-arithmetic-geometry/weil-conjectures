/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
import WeilConjectures.AlgebraicGeometry.Curve.EtaleIdealKernelIso
import WeilConjectures.AlgebraicGeometry.Curve.EtaleNestedIdealKernel
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsRightExact

/-! # Tensor presentation of the kernel of ideal restriction
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- Tensor sections of an ideal identify with its additive vanishing functions.
For nested ideals, the tensor of their inclusion is a kernel of restriction.
There is no cokernel or quasi-coherence-of-the-quotient assumption in this assertion. -/
theorem exists_etaleIdealKernelPresentation (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) :
    ∃ e : (Modules.etaleTensorSectionsFunctor X).obj I.toModules ≅
        kernel (etaleAdditiveSheafToLowerStar I.subschemeι),
      ∃ hzero : ((Modules.etaleTensorSectionsFunctor X).map
          (IdealSheafData.toModulesOfLE hJI) ≫ e.hom) ≫
          (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
            etaleAdditiveSheafToLowerStar J.subschemeι) = 0,
        Nonempty (IsLimit (KernelFork.ofι
          ((Modules.etaleTensorSectionsFunctor X).map
            (IdealSheafData.toModulesOfLE hJI) ≫ e.hom) hzero)) := by
  obtain ⟨eI, eJ, he⟩ := exists_etaleIdealKernelIsoPair X I J hJI
  obtain ⟨k, hk, hz, ⟨hlim⟩⟩ := exists_etaleNestedIdealKernel X I J hJI
  have hmap : eJ.hom ≫ k =
      (Modules.etaleTensorSectionsFunctor X).map
        (IdealSheafData.toModulesOfLE hJI) ≫ eI.hom := by
    apply (cancel_mono (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι))).mp
    simpa only [Category.assoc, hk] using he.symm
  have hzero : ((Modules.etaleTensorSectionsFunctor X).map
      (IdealSheafData.toModulesOfLE hJI) ≫ eI.hom) ≫
      (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
        etaleAdditiveSheafToLowerStar J.subschemeι) = 0 := by
    rw [← hmap, Category.assoc, hz, comp_zero]
  exact ⟨eI, hzero, ⟨IsKernel.isoKernel _ _ hlim eJ hmap⟩⟩

end AlgebraicGeometry.Scheme
