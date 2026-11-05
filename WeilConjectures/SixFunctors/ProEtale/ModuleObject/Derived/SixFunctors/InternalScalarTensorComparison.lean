/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.CategoryTheory.ModuleObjects.MapModMonoidal
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.Monoidal
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarTensorCancellation
import WeilConjectures.CategoryTheory.ModuleObjects.SixFunctors.ScalarExtensionMonoidal

/-!
# The canonical scalar tensor comparison for internal modules

Source: blueprint main-20261015, proper-base-change-rational.proof.md (3), compatibility
of tensor with scalar extension; Stacks 07A4, tensor comparison for change of rings
(blueprint: def-sfb-internal-scalar-tensor-comparison).

The ordinary tensor comparison is specified by its universal property on scalar-unit
pairings. This property determines the entire strong monoidal structure uniquely. The
only postponed data construction uses that unique universal property, rather than an
unspecified isomorphism. The derived comparison is the existing bifunctor-derived lift.

## Main definitions and statements

- `InternalScalarMonoidalNormalized` and `internalScalarMonoidalNormalized_existsUnique`:
  the scalar-unit universal property and its uniqueness.
- `internalScalarMonoidal` and `internalScalar_preservesFlat`: the canonical ordinary
  monoidal structure and preservation of flat modules.
- `internalScalarExtension`: the existing total left derived scalar extension.
- `internalScalarTensorIso` and `internalScalarTensorComparison`: its canonical derived
  tensor isomorphism and underlying natural transformation.
-/

@[expose] public noncomputable section

set_option autoImplicit false

-- Reuse the sheaf and derived closed structures without expanding their constructions.
attribute [local irreducible] DerivedCategory.monoidalClosed CategoryTheory.Mod.monoidalClosed
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Functor.leftDerivedFunctor CategoryTheory.Functor.rightDerivedFunctor

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.CondensedRing

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a] (X : Scheme.{u})

/-- The strong monoidal structure selected by the unique scalar-unit universal property.
Source: Stacks 07A4; blueprint rational proof (3)
(blueprint: def-sfb-internal-scalar-tensor-comparison). -/
@[instance_reducible] def internalScalarMonoidal :
    (Mod.extendScalars (coefficientMap a X)).Monoidal :=
  (internalScalarMonoidalNormalized_existsUnique a X).exists.choose

/-- Extension of scalars preserves flat internal modules.
Source: Stacks 07A4, scalar tensor cancellation; blueprint rational proof (3)
(blueprint: def-sfb-internal-scalar-tensor-comparison).
Proof: tensoring an S-module with S tensor_R M, after restriction to R, is tensoring
that restricted module with M. The balanced tensor cancellation maps are inverse on
pure tensors. Restriction is exact and reflects exactness, so flatness of M gives
exactness of tensoring with its scalar extension. No flatness of S over R is used. -/
@[instance] theorem internalScalar_preservesFlat :
    (Mod.extendScalars (coefficientMap a X)).PreservesFlat := by
  exact Mod.extendScalars_preservesFlat (coefficientMap a X)

/- These structures agree through the recorded instances; their data need not unfold here. -/
attribute [local irreducible] CategoryTheory.Sheaf.monoidalCategory
  CategoryTheory.Mod.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory

variable [∀ Z : Scheme.{u}, PreservesFiniteLimits (Mod.extendScalars (coefficientMap a Z))]

end AlgebraicGeometry.ProEtale.CondensedRing
