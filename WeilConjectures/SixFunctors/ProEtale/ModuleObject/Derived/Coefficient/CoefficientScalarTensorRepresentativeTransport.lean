/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRepresentativeEquation
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

set_option linter.privateModule false

/-! # Transport of scalar tensor representatives

The second strict substep transports the internal-image equation across the exact
section equivalence. It is independent of the bidegree generator calculation.
(blueprint: lem-sfb-coefficient-scalar-tensor-representative-transport)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.Obj ChangeOfRings
namespace AlgebraicGeometry.ProEtale.CondensedRing

attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor
  ModuleRingedComparison.tensor ModuleRingedComparison.qTensor
  coefficientScalarTensorRepresentativeEquation coefficientSectionScalarTotal
  SheafOfModules.scalarPairComplexComparison

universe uc vc w

private theorem map_id_comp
    {A B : Type*} [Category A] [Category B] (F : A ⥤ B)
    {X : A} {Y : B} (f : F.obj X ⟶ Y) : F.map (𝟙 X) ≫ f = f := by
  rw [F.map_id, Category.id_comp]

private theorem app_eq_of_iso
    {A B : Type*} [Category A] [Category B] {F G : A ⥤ B}
    (α β : F ⟶ G) {X Y : A} (e : X ≅ Y) (h : α.app X = β.app X) :
    α.app Y = β.app Y := by
  apply (cancel_epi (F.mapIso e).hom).mp
  change F.map e.hom ≫ α.app Y = F.map e.hom ≫ β.app Y
  rw [α.naturality, β.naturality, h]

attribute [local irreducible] CochainComplex.IsKFlatIndependentCoefficients
  SheafOfModules.IsFlatOnSite

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a]
  [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R Z)]
  [∀ Z : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S Z)]


end AlgebraicGeometry.ProEtale.CondensedRing
