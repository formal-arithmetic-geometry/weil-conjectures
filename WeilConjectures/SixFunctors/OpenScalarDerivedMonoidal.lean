/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.OpenScalarTensorData
import WeilConjectures.CategoryTheory.ExactDerivedMonoidalConstruction
public import WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
public import WeilConjectures.Algebra.Homology.Monoidal.MapHomologicalComplex
public import WeilConjectures.Algebra.Homology.PreservesTotalTensorKFlatQuasiIsoSupplement
import all WeilConjectures.Algebra.Homology.RingedDerivedTensorNativeSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtaleTensorPullbackModels
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic

/-! # Native derived monoidal pro-etale pullback

Source: Stacks Project, Tags 07A4 and 0FPT.
(blueprint: lem-sp-open-scalar-derived-monoidal).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option linter.style.haveILetI false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open AlgebraicGeometry AlgebraicGeometry.Scheme SheafOfModules WeilConjectures
namespace AlgebraicGeometry.ProEtale.OpenScalarTensor

attribute [local instance 20000] instMonoidalCategoryHomologicalComplexIntUp_weilConjectures
  SheafOfModules.cochainModulesMonoidal
  SheafOfModules.cochainModulesSymmetric SheafOfModules.cochainModulesPreadditive


set_option maxHeartbeats 2000000 in
-- Compare the algebraic inverse-image presentation with its universe-indexed version.
private theorem ordinary_preservesFlat {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S) :
    @Functor.PreservesFlat (proEtaleRingModules Y R) (proEtaleRingModules X S) _ _
      (SheafOfModules.cochainModulesMonoidal R) (SheafOfModules.cochainModulesMonoidal S)
      (proEtaleRingModulePullback f R S c) := by
  letI := SheafOfModules.cochainModulesMonoidal R
  letI := SheafOfModules.cochainModulesMonoidal S
  refine ⟨fun {M} hM ↦ ?_⟩
  let e : siteSheafTensorRight.{u, u + 1, u + 1, u + 1} (A := R) M ≅ tensorRight M :=
    siteSheafTensorRightIso.{u + 1, u, u + 1} (J := Scheme.ProEt.topology Y) R M
  have hm : IsFlatOnSite (J := Scheme.ProEt.topology Y) (R := R) M :=
    (exactFunctor _ _).prop_of_iso e.symm hM.tensorRight
  let I := modelNormalizedAlgebraicLift f R
  have : PreservesFiniteLimits (proEtaleSheafInverseImage f (Type (u + 1))) :=
    (AlgebraicGeometry.ProEtale.toposFunctorialityInverseImage f (𝟙 Y)).2.2.2.1
  have hn := isFlat_ringedToposPullback.{u + 1, u, u + 1, u, u + 1, u + 1}
    (proEtaleSheafInverseImage f (Type (u + 1)))
    (proEtaleSheafDirectImage f (Type (u + 1)))
    (proEtaleSheafAdjunction f (Type (u + 1))) (inverseImageOfUniverses I) c.hom M hm
  have hn' : IsFlatOnSite (J := Scheme.ProEt.topology X) (R := S)
      ((proEtaleRingModulePullback f R S c).obj M) := by
    have hobj : (proEtaleRingModulePullback f R S c).obj M =
        changeOfRings c.hom (I.modules.obj M) := rfl
    rw [hobj, changeOfRings_eq_ofUniverses]
    exact hn
  have ht : exactFunctor _ _ (tensorRight ((proEtaleRingModulePullback f R S c).obj M)) :=
    (exactFunctor _ _).prop_of_iso
      (siteSheafTensorRightIso S ((proEtaleRingModulePullback f R S c).obj M)) hn'
  refine ⟨?_, ht⟩
  exact (exactFunctor _ _).prop_of_iso
    (NatIso.ofComponents (fun N ↦ β_ N ((proEtaleRingModulePullback f R S c).obj M))
      (by intros; simp)) ht

/-- Exact geometric pullback has a native derived monoidal structure whose tensorator
satisfies the localization square on K-flat complexes.
Source: Stacks Project, Tags 07A4 and 0FPT
(blueprint: lem-sp-open-scalar-derived-monoidal).

Proof: flatness on the ringed site agrees with exactness of tensoring in the ordinary
module monoidal category. Ringed-topos pullback preserves site-flat modules, so it
preserves flat objects for this monoidal structure. The pro-etale module pullback is
exact and is a left adjoint; hence it preserves the colimits used for flat resolutions.
Apply the normalized exact derived-monoidal construction with the native flat-resolution
and closed structures. Its localization square is the asserted equation. -/
theorem derived_monoidal {X Y : Scheme.{u}} (f : X ⟶ Y)
    (R : Sheaf (Scheme.ProEt.topology Y) CommRingCat.{u + 1})
    (S : Sheaf (Scheme.ProEt.topology X) CommRingCat.{u + 1})
    (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
    (m : (proEtaleRingModulePullback f R S c).Monoidal) :
    letI : (proEtaleRingModulePullback f R S c).IsLeftAdjoint :=
      (proEtaleRingModuleAdjunction f R S c).isLeftAdjoint
    letI := m
    letI := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology Y) R
    letI := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2}
      (Scheme.ProEt.topology X) S
    ∃ n : (proEtaleRingDerivedPullback f R S c).Monoidal, letI := n
      ∀ P Q : CochainComplex (proEtaleRingModules Y R) ℤ,
        P.IsKFlatForTotalTensor → Q.IsKFlatForTotalTensor →
          Functor.OplaxMonoidal.δ (proEtaleRingDerivedPullback f R S c)
              (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj Q) ≫
            ((proEtaleRingModulePullback f R S c).mapDerivedCategoryFactors.hom.app P ⊗ₘ
              (proEtaleRingModulePullback f R S c).mapDerivedCategoryFactors.hom.app Q) ≫
            Functor.LaxMonoidal.μ DerivedCategory.Q
              (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj P)
              (((proEtaleRingModulePullback f R S c).mapHomologicalComplex (.up ℤ)).obj Q) =
          (proEtaleRingDerivedPullback f R S c).map
              (Functor.LaxMonoidal.μ DerivedCategory.Q P Q) ≫
            (proEtaleRingModulePullback f R S c).mapDerivedCategoryFactors.hom.app (P ⊗ Q) ≫
            DerivedCategory.Q.map
              (Functor.mapCochainComplexμIso (proEtaleRingModulePullback f R S c) P Q).inv := by
  letI := m
  letI := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2}
    (Scheme.ProEt.topology Y) R
  letI := RingedDerivedNative.monoidal.{u + 1, u, u + 1, u + 2}
    (Scheme.ProEt.topology X) S
  letI : IsGrothendieckAbelian.{u+1} (proEtaleRingModules Y R) :=
    RingedDerivedNative.moduleGrothendieck.{u+1,u,u+1} (Scheme.ProEt.topology Y) R
  letI : IsGrothendieckAbelian.{u+1} (proEtaleRingModules X S) :=
    RingedDerivedNative.moduleGrothendieck.{u+1,u,u+1} (Scheme.ProEt.topology X) S
  letI : Abelian.HasFunctorialFlatResolution (proEtaleRingModules Y R) :=
    RingedDerivedNative.moduleFlat.{u+1,u,u+1} (Scheme.ProEt.topology Y) R
  letI : Abelian.HasFunctorialFlatResolution (proEtaleRingModules X S) :=
    RingedDerivedNative.moduleFlat.{u+1,u,u+1} (Scheme.ProEt.topology X) S
  letI : MonoidalClosed (proEtaleRingModules Y R) :=
    RingedDerivedNative.moduleClosed.{u+1,u,u+1} (Scheme.ProEt.topology Y) R
  letI : MonoidalClosed (proEtaleRingModules X S) :=
    RingedDerivedNative.moduleClosed.{u+1,u,u+1} (Scheme.ProEt.topology X) S
  let L := proEtaleRingModulePullback f R S c
  letI : L.PreservesFlat := ordinary_preservesFlat f R S c
  have : L.IsLeftAdjoint := (proEtaleRingModuleAdjunction f R S c).isLeftAdjoint
  obtain ⟨n, hn⟩ := ConstantModuleDerivedProjection.exact_monoidal_normalization L m
  exact ⟨n, hn⟩

end AlgebraicGeometry.ProEtale.OpenScalarTensor
