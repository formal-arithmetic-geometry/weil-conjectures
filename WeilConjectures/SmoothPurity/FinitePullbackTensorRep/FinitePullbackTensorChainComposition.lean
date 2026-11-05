/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SmoothPurity.FinitePullbackTensorRep.FinitePullbackTensorRepresentativeData
import WeilConjectures.AlgebraicGeometry.Finite.FiniteIntrinsicPullbackUnitComposition
import all WeilConjectures.Algebra.Homology.ScalarHomOrdinary.ScalarHomOrdinaryTensorComparisonSupplement
import all WeilConjectures.AlgebraicGeometry.ProEtale.Tensor.ProEtaleTensorPullbackModels
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits

/-! # Composition of the ordinary signed tensor comparison

Source: Stacks 03EL, 07A4 and 00YV.
(blueprint: lem-pur-finite-pullback-tensor-chain-composition).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
attribute [local implicit_reducible] AlgebraicGeometry.Scheme.ProEt
  CategoryTheory.MorphismProperty
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
attribute [-instance] WeilConjectures.integralOperationsSiteSmall
universe u
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local implicit_reducible] proEtaleConstantModuleDirectImage
  proEtaleRingModuleDirectImage SheafOfModules.pushforward
  PresheafOfModules.pushforward PresheafOfModules.pushforward₀
  PresheafOfModules.pushforward₀Obj PresheafOfModules.restrictScalars
  PresheafOfModules.restrictScalarsObj ModuleCat.restrictScalars
  ModuleCat.RestrictScalars.obj'

namespace WeilConjectures.FinitePullbackTensorRep
attribute [local irreducible] Scheme.residueField finiteIntrinsicClosed
  finiteIntrinsicTensorModels finitePullbackTensorConstruction
attribute [local implicit_reducible] integralCoefficientSheaf
  integralCoefficientCommRingSheaf finiteIntrinsicDerivedTensor
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

attribute [local irreducible] moduleComp proEtaleOrdinaryTensorPullback
  SheafOfModules.monoidalCategory

attribute [local instance] modules_abelian ordinary_additive
attribute [local implicit_reducible] modules_abelian
attribute [local semireducible] pull
attribute [local implicit_reducible] pull Functor.map₂HomologicalComplex
  Functor.mapHomologicalComplex

attribute [local instance high] tensor_additive tensor_obj_additive

attribute [local instance high] tensor_zero tensor_obj_zero

@[irreducible] private def kappa {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) :
    tensor l E X n ((pull l E f n).obj P) ((pull l E f n).obj Q) ≅
      (pull l E f n).obj (tensor l E Y n P Q) :=
  proEtaleTensorPullbackTotalIso f (integralCoefficientCommRingSheaf l E Y n)
    (integralCoefficientCommRingSheaf l E X n) (pullbackTensorCoefficientIso l E f n) P Q

attribute [local instance] modules_abelian ordinary_additive
attribute [local implicit_reducible] totalTensor

@[reassoc] private theorem inclusion_kappa {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (P Q : CochainComplex (normalizedDVRModules l E Y n) ℤ) (i j k : ℤ)
    (hij : ComplexShape.π (.up ℤ) (.up ℤ) (.up ℤ) (i, j) = k) :
    inclusion l E X n ((pull l E f n).obj P) ((pull l E f n).obj Q) i j k hij ≫
        (kappa l E f n P Q).hom.f k =
      (mu l E f n (P.X i) (Q.X j)).inv ≫
        (ordinary l E f n).map (inclusion l E Y n P Q i j k hij) := by
  simp only [inclusion, kappa, proEtaleTensorPullbackTotalIso, asIso_hom,
    proEtaleTensorPullbackTotal, tensorPullbackTotal, tensorPullbackTotalComponent,
    pull, Functor.mapHomologicalComplex_obj_X, HomologicalComplex.ι_mapBifunctorDesc]

end WeilConjectures.FinitePullbackTensorRep
