/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteNativeTensor.FiniteNativeEtaleProjection

public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCtfInternalEtaleRealization
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteOrdinaryEquivalence
public import WeilConjectures.CategoryTheory.Adjunction.SixFunctors.FiniteCoefficientTensorPullbackEncoding
public import WeilConjectures.AlgebraicGeometry.Finite.Compact.FiniteCompactSiteCoherence
public import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
public import WeilConjectures.CategoryTheory.SuppliedExchangeProjection.ExchangeProjectionSuppliedDomains
public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothTensorDuality
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ExceptionalInverseImageExistence
public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.ModuleRingedToposDerivedComparison
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.OpenImmersionProjection
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekLocality
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonUpperStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ComparisonMonoidal
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartEncoding
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteCoefficientHeartTensor
public import WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinary.FiniteDiscreteEncodingCompactification
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedComp
public import WeilConjectures.CategoryTheory.ExactMonoidalEquivalenceDerived.ExactMonoidalEquivalenceDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure
public import WeilConjectures.SixFunctors.Supporting.ModCondensedCachedInstances

/-! # Finite native tensor comparison

Source: the current blueprint, sk-prop-sp-composition, finite tensor maps, and
sk-thm-purity-transport, Steps 1 and 3.
(blueprint: lem-pur-finite-native-tensor-comparison).
-/

/-! The canonical comparison data are kept together so the domain construction,
operation comparison and geometric compositor normalization can be imported independently.
All pre-existing declarations below retain their signatures. The etale projection uses
the literal upstream component through a wrapper elaborated in its native import context.
The ordinary native projection retains the upstream bifunctor before evaluation.
(blueprint: def-pur-finite-native-tensor-comparison-data).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj CategoryTheory.Functor
open scoped AlgebraicGeometry.ProEtale.CondensedRing.CachedModInstances

namespace AlgebraicGeometry.ProEtale.FiniteNativeTensor
open FiniteDiscreteOrdinary
-- Discard the imported instance with a free coefficient universe.
attribute [-instance] WeilConjectures.scalarReductionSiteSmall
attribute [local instance 20000] sheafBraidedCategory sheafSymmetricCategory
  sheafMonoidalCategory sheafMonoidalClosed
  preservesColimitsOfSize_tensorLeft_sheaf preservesColimitsOfSize_tensorRight_sheaf
attribute [local instance 2000] Mod.monoidalCategory Mod.monoidalClosed
attribute [local irreducible] Mod.monoidalClosed
attribute [local irreducible] Sheaf.monoidalCategory SheafOfModules.monoidalCategory

variable (A : Type u) [CommRing A] [Finite A]
  [TopologicalSpace A] [DiscreteTopology A] [IsTopologicalRing A]

by
  let NX := (E X).ordinary.functor ⋙ (E X).fixed.functor
  let NY := (E Y).ordinary.functor ⋙ (E Y).fixed.functor
  exact Functor.isoWhiskerRight NY.leftDerivedFunctorIsoMapDerivedCategory.symm _ ≪≫
    Functor.leftDerivedFunctorCompNatIso
      (CondensedRing.upperStar (coefficient A) f) NX NY
      (upperStar (ModuleCat.{u + 1} (ULift.{u + 1} A)) f)
      (nativeencodingPullbackIso A f (E Y) (E X)).symm ≪≫
    Functor.isoWhiskerLeft _ NX.leftDerivedFunctorIsoMapDerivedCategory

/-- The literal ordinary compactification projection as a natural transformation.
Source: `ProEtale.projectionMapOfCompactification`.
(blueprint: def-pur-finite-native-tensor-comparison-data).

This is the published proper-mate/open projection itself, with its source and target
written using the native functor aliases. Evaluating it twice recovers the ordinary
branch of nativeP. Retaining the bifunctor makes its naturality available without
re-elaborating the projection's hidden coefficient instances.
-/
def nativeOrdinaryProjection {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    nativeCompact A true c ⋙ curriedTensor (Native A true Y) ⟶
      (Functor.postcompose₂.obj (nativeCompact A true c)).obj
        ((((Functor.whiskeringLeft₂ _).obj (𝟭 _)).obj (nativeUpper A true f)).obj
          (curriedTensor (Native A true X))) := by
  exact projectionMapOfCompactification
    (ModuleCat.{u + 1} (ULift.{u + 1} A)) c

section Categorical

variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
  [MonoidalCategory C] [MonoidalCategory D]
  [MonoidalCategory C'] [MonoidalCategory D']

end Categorical

attribute [instance_reducible] DomainComparison.monoidal

attribute [instance] DomainComparison.etaleMonoidal DomainComparison.nativeMonoidal
  DomainComparison.monoidal DomainComparison.equivalence

section Restriction
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]

variable [MonoidalCategory C] [MonoidalCategory D]

end Restriction

by
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let L := etalePlus A X M
  let a := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ cf).app L
  let b := (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ cg).app
    ((Etale.rightDerivedLowerShriekOfCompactificationPlus Λ cf).obj L)
  exact ((etaleF A cg).mapIso a).symm ≪≫ b.symm ≪≫
    DerivedCategory.Plus.ι.mapIso
      ((coherenceEtaleCompositor (ULift.{u + 1} A) cf cg ch).app L) ≪≫
    (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ ch).app L

by
  let Λ := ModuleCat.{u + 1} (ULift.{u + 1} A)
  let L := etalePlus A X M
  let N := (comparisonUpperStar Λ X).mapDerivedCategoryPlus.obj L
  let w := (comparisonUpperStar Λ X).mapDerivedCategoryPlusCompatibility.app L
  let Pf := rightDerivedLowerShriekOfCompactification Λ cf
  let Pg := rightDerivedLowerShriekOfCompactification Λ cg
  let Ph := rightDerivedLowerShriekOfCompactification Λ ch
  let a := (rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ cf).app N
  let b := (rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ cg).app
    ((rightDerivedLowerShriekOfCompactificationPlus Λ cf).obj N)
  let d := (rightDerivedLowerShriekOfCompactificationPlusCompatibility Λ ch).app N
  exact (Pg.mapIso (Pf.mapIso w)).inv ≫ (Pg.mapIso a).inv ≫ b.inv ≫
    DerivedCategory.Plus.ι.map
      (finiteCompactSiteCompositionPlus (ULift.{u + 1} A) cf cg ch T L) ≫
    d.hom ≫ (Ph.mapIso w).hom

section CompositorMate
variable {C : Type u₁} {D : Type u₂} {H : Type u₃}
  {C' : Type u₄} {D' : Type u₅} {H' : Type u₆}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} H]
  [Category.{v₄} C'] [Category.{v₅} D'] [Category.{v₆} H']

end CompositorMate

end AlgebraicGeometry.ProEtale.FiniteNativeTensor
