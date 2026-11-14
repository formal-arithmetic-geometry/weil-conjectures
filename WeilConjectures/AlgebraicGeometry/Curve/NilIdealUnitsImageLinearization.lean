/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsSheaf
import WeilConjectures.AlgebraicGeometry.Curve.NilIdealUnitsAdditiveImageComparison
import WeilConjectures.AlgebraicGeometry.Curve.AdditiveIdealImageTensorComparison
import WeilConjectures.CategoryTheory.Sites.Torsor

/-! # Linearization of the image of nilpotent units modulo an ideal
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

/-- For nil ideals `J ≤ I` with `I * I ≤ J`, the image of the units congruent to one
modulo `I` in the units on the subscheme defined by `J` is the additive sheaf of `I/J`. -/
theorem nonempty_nilIdealUnitsImageIso (X : Scheme.{u}) (I J : X.IdealSheafData)
    (hJI : J ≤ I) (hII : I * I ≤ J) (hIN : I ≤ X.nilradical)
    [(cokernel (IdealSheafData.toModulesOfLE hJI)).IsQuasicoherent] :
    Nonempty (image (kernel.ι (gmSheafToLowerStarGmSheaf I.subschemeι) ≫
        gmSheafToLowerStarGmSheaf J.subschemeι) ≅
      ((sheafCompose X.smallEtaleTopology AddCommGrpCat.uliftFunctor.{u + 1, u}).obj
        (Modules.etaleTensorSectionsSheaf
          (cokernel (IdealSheafData.toModulesOfLE hJI))))) := by
  obtain ⟨unitsToAdditive⟩ :=
    nonempty_nilIdealUnitsAdditiveImageIso X I J hJI hII hIN
  obtain ⟨additiveToTensor⟩ := nonempty_additiveIdealImageTensorIso X I J hJI
  exact ⟨unitsToAdditive.trans additiveToTensor⟩

end AlgebraicGeometry.Scheme
