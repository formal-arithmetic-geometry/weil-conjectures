/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.DivisorIdealSheaf
public import WeilConjectures.AlgebraicGeometry.Curve.EtaleAdditiveStructureSheaf
public import WeilConjectures.AlgebraicGeometry.EtaleTensorSectionsRightExact
import WeilConjectures.AlgebraicGeometry.Curve.EtaleIdealSectionsKernel
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-! # Tensor ideal identifications compatible with inclusion
-/

@[expose] public section

universe u
open CategoryTheory Limits
namespace AlgebraicGeometry.Scheme

private theorem idealKernelIso {X : Scheme.{u}} (I : X.IdealSheafData) :
    ∃ e : (Modules.etaleTensorSectionsFunctor X).obj I.toModules ≅
        kernel (etaleAdditiveSheafToLowerStar I.subschemeι),
      e.hom ≫ kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) =
        (presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
            (etaleIdealSectionsInclusion I) ≫
          (sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).counit.app
            X.etaleAdditiveSheaf := by
  classical
  let f := etaleAdditiveSheafToLowerStar I.subschemeι
  let l := etaleIdealSectionsInclusion I
  have hz : l ≫ f.hom = 0 := by
    apply NatTrans.ext
    funext U
    exact (etaleIdealSectionsInclusion_isKernel I U).choose
  let c := KernelFork.ofι l hz
  have hc : IsLimit c := by
    apply evaluationJointlyReflectsLimits
    intro U
    let hU := (etaleIdealSectionsInclusion_isKernel I U).choose_spec.some
    exact (KernelFork.isLimitMapConeEquiv c
      ((CategoryTheory.evaluation X.Etaleᵒᵖ AddCommGrpCat.{u + 1}).obj U)).symm hU
  let S := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let adj := sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let eO := asIso (adj.counit.app X.etaleAdditiveSheaf)
  let eZ := asIso (adj.counit.app ((Etale.lowerStar AddCommGrpCat.{u + 1}
    I.subschemeι).obj I.subscheme.etaleAdditiveSheaf))
  have hn : S.map f.hom ≫ eZ.hom = eO.hom ≫ f := adj.counit.naturality f
  have hiff {W : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
      (φ : W ⟶ S.obj X.etaleAdditiveSheaf.obj) :
      φ ≫ S.map f.hom = 0 ↔ φ ≫ eO.hom ≫ f = 0 := by
    rw [← hn, ← Category.assoc, ← cancel_mono eZ.hom, zero_comp]
  let hlim := KernelFork.isLimitOfIsLimitOfIff (c.mapIsLimit hc S) f eO (fun {_} φ ↦ hiff φ)
  let e := hlim.conePointUniqueUpToIso (kernelIsKernel f)
  refine ⟨e, ?_⟩
  exact hlim.conePointUniqueUpToIso_hom_comp (kernelIsKernel f) WalkingParallelPair.zero

/-- Tensor sections identify with additive ideal kernels, compatibly with nested inclusion. -/
theorem exists_etaleIdealKernelIsoPair (X : Scheme.{u})
    (I J : X.IdealSheafData) (hJI : J ≤ I) :
    ∃ eI : (Modules.etaleTensorSectionsFunctor X).obj I.toModules ≅
        kernel (etaleAdditiveSheafToLowerStar I.subschemeι),
      ∃ eJ : (Modules.etaleTensorSectionsFunctor X).obj J.toModules ≅
          kernel (etaleAdditiveSheafToLowerStar J.subschemeι),
        (Modules.etaleTensorSectionsFunctor X).map (IdealSheafData.toModulesOfLE hJI) ≫
            eI.hom ≫ kernel.ι (etaleAdditiveSheafToLowerStar I.subschemeι) =
          eJ.hom ≫ kernel.ι (etaleAdditiveSheafToLowerStar J.subschemeι) := by
  obtain ⟨eI, heI⟩ := idealKernelIso I
  obtain ⟨eJ, heJ⟩ := idealKernelIso J
  refine ⟨eI, eJ, ?_⟩
  rw [heI, heJ, ← Category.assoc]
  congr 1
  let S := presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  change S.map (Functor.whiskerRight
      ((Modules.etaleTensorSectionsPresheafFunctor X).map
        (IdealSheafData.toModulesOfLE hJI)) AddCommGrpCat.uliftFunctor) ≫
    S.map (etaleIdealSectionsInclusion I) = S.map (etaleIdealSectionsInclusion J)
  rw [← S.map_comp]
  congr 1
  unfold etaleIdealSectionsInclusion
  rw [← Functor.whiskerRight_comp, ← Category.assoc, ← Functor.map_comp,
    IdealSheafData.toModulesOfLE_toModulesι]

end AlgebraicGeometry.Scheme
