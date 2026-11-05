/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ModuleRingedComparison.SectionModuleOperationsData
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence
import WeilConjectures.AlgebraicGeometry.InverseImageModuleFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FinalRingedUnitMate
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedDirectImagePairingLax
public import WeilConjectures.AlgebraicGeometry.ProEtaleSectionModuleFunctors

import WeilConjectures.AlgebraicGeometry.InternalModuleOperations.InternalModuleOperationsTransportSupplement
import all WeilConjectures.CategoryTheory.InternalSectionTensorComparison
import all WeilConjectures.CategoryTheory.InternalAbelianSheafModuleEquivalence
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.CategoryTheory.Monoidal.Internal.FunctorCategory
import all WeilConjectures.CategoryTheory.RingObjects.Ab
import all WeilConjectures.CategoryTheory.Sites.MonObj
import all WeilConjectures.CategoryTheory.ModuleObjects.MapMod
import all WeilConjectures.CategoryTheory.SheafTensor
import all WeilConjectures.CategoryTheory.SheafTensorStructure
import all Mathlib.CategoryTheory.Sites.Monoidal
import all Mathlib.CategoryTheory.Abelian.Basic
import all Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.CategoryTheory.PresheafTensorInternalHom
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Sites.Localization
import all Mathlib.CategoryTheory.Sites.ConstantSheaf
import all Mathlib.CategoryTheory.Sites.Sheafification
import all Mathlib.CategoryTheory.Adjunction.Limits
import all Mathlib.CategoryTheory.Monoidal.Braided.Reflection
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import all WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all WeilConjectures.CategoryTheory.ModuleObjects.Symmetric
import all WeilConjectures.CategoryTheory.ModuleObjects.Abelian
import all WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import all WeilConjectures.FromJoel.Algebra.Homology.TotalComplexMap
import all WeilConjectures.CategoryTheory.InternalSectionModuleFlat
import all WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import WeilConjectures.CategoryTheory.Abelian.Flat.PreservesFlat
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.LowerShriek.Defs

/-! # Normalized tensors on the existing pro-etale module functors

Source: Stacks Project, Sites, Tag 00YV; Modules on Sites, Tags 03EK, 03EL,
03D7, 03DI and 03DJ; Cohomology on Sites, Tags 07A4, 07A6 and 0B56
(blueprint: def-pd-proetale-section-module-functors).

## Main definitions

- `coefficientMap`: the structural section-ring map adjunct to the condensed coefficient map.
- `pushforward`, `pullback`, `adjunction`: the actual ringed module operations and adjunction.
- `ordinaryTensorComparison`, `totalComparison`: uniquely normalized tensor comparisons.
- `pushforwardComposition`, `pullbackComposition`: geometric pasting and its adjunction mate.
- `extension`, `openAdjunction`: the actual open extension and restriction adjunction.

-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

attribute [local irreducible] SheafOfModules.tensorObjIsoSheafification
  PresheafOfModules.sheafificationAdjunction

attribute [local irreducible] Mod.monoidalCategoryStruct
  InternalAbelianSheafModule.comparison_tensorIso
  InternalAbelianSheafModule.comparison_unitIso
  InternalAbelianSheafModule.comparison_totalIso

attribute [local irreducible] Adjunction.leftAdjointOplaxMonoidal
  Adjunction.rightAdjointLaxMonoidal

attribute [local irreducible] canonicalInternalPush CondensedRing.monoidal_upperStar
  Mod.extendScalars CondensedRing.upperStarLowerStarAdjunction

private theorem existsUnique_of_normalized_pairing {A : Sort*} {P Q : A → Prop}
    (h : ∃ a, P a ∧ Q a ∧ ∀ b, P b → b = a) : ∃! a, P a := by
  obtain ⟨a, ha, _, hu⟩ := h
  exact ⟨a, ha, hu⟩

attribute [local irreducible] Mod.inducingFunctorData SheafOfModules.monoidalCategory

attribute [local irreducible] ordinaryTensorComparison

section PullTensorProof

section PullTensorTransport

set_option backward.isDefEq.respectTransparency true

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄

variable {A : Type u₁} [Category.{v₁} A] [MonoidalCategory A]
  {B : Type u₂} [Category.{v₂} B] [MonoidalCategory B]
  {A' : Type u₃} [Category.{v₃} A'] [MonoidalCategory A']
  {B' : Type u₄} [Category.{v₄} B'] [MonoidalCategory B']

end PullTensorTransport

section GeneratorFormula

universe w v v'

-- Upstream made these instances local (InternalSectionTensorComparison, SheafTensor).
attribute [local instance] Sheaf.monoidalCategory Sheaf.symmetricCategory
attribute [local instance] sfbSheafTensor_monoidalPreadditive sfbSheafTensor_hasWeakSheafify

end GeneratorFormula

attribute [local irreducible] internalPushLax pushLax
  InternalAbelianSheafModule.comparison_internalTmul
  InternalAbelianSheafModule.comparison_sectionTmul
  InternalModuleOperations.lowerComparison InternalModuleOperations.upperComparison

attribute [local irreducible] InternalAbelianSheafModule.sectionModuleEquivalence

end PullTensorProof

attribute [local irreducible] internalPullMonoidal pullMonoidal
  internalPushLax pushLax internalPullOplax pullOplax

attribute [local instance 4000] total_preserves

set_option backward.isDefEq.respectTransparency true in
set_option maxHeartbeats 600000 in
-- The concrete total tensors carry large category and universe instances.
/-- Extension by zero is additive, since all its three specified factors are additive.
Source: Stacks 03DJ (blueprint: def-pd-proetale-section-module-functors).
Proof: its underlying maps are extension-by-zero maps of abelian sheaves; addition
is computed on each summand before sheafification. -/
@[instance] theorem extension_additive {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : (extension Λ j).Additive := by
  exact (openAdjunction Λ j).left_adjoint_additive

/-- Extension by zero preserves finite limits.
Source: Stacks 03DJ (blueprint: def-pd-proetale-section-module-functors).
Proof: exactness of the internal open extension transfers through the two exact
equivalences, or can be checked on the unchanged underlying abelian sheaves. -/
@[instance] theorem extension_preservesFiniteLimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteLimits (extension Λ j) := by
  exact ((InternalModuleOperations.internal_module_operations_transport Λ).2.2.2.2.1 j).1.mp
    (inferInstance : PreservesFiniteLimits (CondensedRing.openImmersionLowerShriek Λ j))

/-- Extension by zero preserves finite colimits.
Source: Stacks 03DJ (blueprint: def-pd-proetale-section-module-functors).
Proof: it is the left adjoint in the specified open adjunction. -/
@[instance] theorem extension_preservesFiniteColimits {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] : PreservesFiniteColimits (extension Λ j) := by
  let := (openAdjunction Λ j).isLeftAdjoint
  exact inferInstance

end AlgebraicGeometry.ProEtale.ModuleRingedComparison
