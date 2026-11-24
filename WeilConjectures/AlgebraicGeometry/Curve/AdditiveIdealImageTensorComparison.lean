/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.AlgebraicGeometry.Curve.EtaleIdealKernelPresentation
import Mathlib.CategoryTheory.Abelian.Exact

/-! # The additive ideal image and tensor sections
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- For J contained in I, the additive image of the ideal of I on the subscheme of J
is the etale sheaf associated with the specified module cokernel J to I.
There is no nilpotence or square-zero hypothesis in this additive assertion. -/
theorem nonempty_additiveIdealImageTensorIso (X : Scheme.{u}) (I J : X.IdealSheafData)
    (hJI : J ≤ I) [(cokernel (IdealSheafData.toModulesOfLE hJI)).IsQuasicoherent] :
    Nonempty (image (kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
        etaleAdditiveSheafToLowerStar J.subschemeι) ≅
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf
          (cokernel (IdealSheafData.toModulesOfLE hJI))))) := by
  let T := Modules.etaleTensorSectionsFunctor X
  let a := IdealSheafData.toModulesOfLE hJI
  let f := kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) ≫
    etaleAdditiveSheafToLowerStar J.subschemeι
  obtain ⟨e, hz, ⟨hk⟩⟩ := exists_etaleIdealKernelPresentation X I J hJI
  let S := ShortComplex.mk (T.map a ≫ e.hom) f hz
  have hS : S.Exact := ShortComplex.exact_of_f_is_kernel S hk
  let e₁ : cokernel (T.map a ≫ e.hom) ≅ image f :=
    IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel _) hS.isColimitImage
  let e₂ : cokernel (T.map a) ≅ cokernel (T.map a ≫ e.hom) :=
    cokernel.mapIso _ _ (Iso.refl _) e (by simp)
  have : PreservesColimitsOfShape WalkingParallelPair T :=
    Modules.preservesCokernels_etaleTensorSectionsFunctor X
  exact ⟨e₁.symm ≪≫ e₂.symm ≪≫ (PreservesCokernel.iso T a).symm ≪≫
    Modules.etaleTensorSectionsFunctorObjIso (cokernel a)⟩

end AlgebraicGeometry.Scheme
