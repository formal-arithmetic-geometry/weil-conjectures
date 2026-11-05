/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorData
import WeilConjectures.AlgebraicGeometry.IntegralResidueDerivedMonoidal
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.MonoidalStructure

/-! # Canonical normalized scalar tensor -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u v w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Obj

section CachedGenericStructures
variable {C : Type*} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [MonoidalCategory C]
  [MonoidalPreadditive C] [MonoidalClosed C] [BraidedCategory C]
  [Abelian.HasFunctorialFlatResolution C]
end CachedGenericStructures
attribute [local instance 2000] cachedComplexMonoidal cachedHomotopyMonoidal
  cachedDerivedMonoidal

attribute [local instance 3000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
attribute [local instance 4000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
attribute [local instance 5000]
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

set_option backward.defeqAttrib.useBackward true
attribute [local instance 20000] AlgebraicGeometry.ProEtale.sheafBraidedCategory
attribute [local implicit_reducible]
  CategoryTheory.GrothendieckTopology.monoidalCategory_sheaf_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.braidedCategory_sheaf_of_essentiallySmall
  CategoryTheory.GrothendieckTopology.symmetricCategory_sheaf_of_essentiallySmall
  AlgebraicGeometry.ProEtale.sheafMonoidalCategory
  AlgebraicGeometry.ProEtale.sheafBraidedCategory
  AlgebraicGeometry.ProEtale.sheafSymmetricCategory
  CategoryTheory.Sheaf.symmetricCategory CategoryTheory.Sheaf.braidedCategory

/-- The existing sheaf symmetry with its native braiding retained explicitly.
Source: sheaf symmetric tensor (blueprint: lem-sfb-quotient-scalar-tensor-canonical). -/
@[instance_reducible] def AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarSheafSymmetric
    (T : AlgebraicGeometry.Scheme.{u}) :
    SymmetricCategory (Sheaf (AlgebraicGeometry.Scheme.ProEt.topology T) Ab.{u + 1}) :=
  { toBraidedCategory := AlgebraicGeometry.ProEtale.sheafBraidedCategory Ab.{u + 1} T
    symmetry := fun M N ↦ @SymmetricCategory.symmetry _ _ _
      (AlgebraicGeometry.ProEtale.sheafSymmetricCategory T) M N }

attribute [local instance 21000]
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarSheafSymmetric

/-- The existing closed structure on internal modules, with structural arguments shared.
Source: the relative module tensor (blueprint: lem-sfb-quotient-scalar-tensor-canonical). -/
@[instance_reducible] def AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleClosed
    (B : CategoryTheory.Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] (T : AlgebraicGeometry.Scheme.{u}) :
    MonoidalClosed (AlgebraicGeometry.ProEtale.QuotientChange.Modules B T) := inferInstance

/-- The existing braiding on internal modules, with the ambient sheaf structure shared.
Source: the symmetric module tensor (blueprint: lem-sfb-quotient-scalar-tensor-canonical). -/
@[instance_reducible] def AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleBraided
    (B : CategoryTheory.Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] (T : AlgebraicGeometry.Scheme.{u}) :
    BraidedCategory (AlgebraicGeometry.ProEtale.QuotientChange.Modules B T) := inferInstance

attribute [local instance 2000]
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleClosed
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleBraided
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarModuleFlat
  AlgebraicGeometry.ProEtale.QuotientSectionTensor.scalarPreservesKFlat

attribute [local irreducible] cochainCompute

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory
  DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

attribute [local instance] AlgebraicGeometry.ProEtale.CondensedRing.projectionDerivedMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleAbelian
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleHasDerived
  AlgebraicGeometry.ProEtale.CondensedRing.projectionSheafMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.projectionCoefficientMonObj
  AlgebraicGeometry.ProEtale.CondensedRing.projectionModuleCategory

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj ChangeOfRings

namespace AlgebraicGeometry.ProEtale.QuotientSectionTensor

open QuotientChange IntegralQuotient

variable {Λ Λ' : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj Λ] [IsCommMonObj Λ] [MonObj Λ'] [IsCommMonObj Λ']
  (a : Λ ⟶ Λ') [IsMonHom a]

open ModuleRingedComparison

/-- The actual bifunctor-derived scalar tensorator, uncurried to pairs.
Source: Stacks 07A4 (blueprint: lem-sfb-quotient-scalar-tensor-canonical). -/
@[irreducible] def canonicalTensor (T : Scheme.{u}) : TensorIso a T := by
  let := scalarModuleClosed Λ T
  let := scalarModuleClosed Λ' T
  let := scalarModuleBraided Λ T
  let := scalarModuleBraided Λ' T
  let := scalarModuleFlat Λ T
  let := scalarModuleFlat Λ' T
  have := scalarPreservesKFlat a T
  let := CondensedRing.internalScalarMonoidal a T
  unfold TensorIso D CondensedRing.derivedTensor
  have := CondensedRing.internalScalar_preservesFlat a T
  let δ := (extension a T).leftDerivedTensorComparison
  have hδ : IsIso δ := (extension a T).isIso_leftDerivedTensorComparison
  exact uncurryTensorIso _ _ _ (@asIso _ _ _ _ δ hδ)

end AlgebraicGeometry.ProEtale.QuotientSectionTensor
