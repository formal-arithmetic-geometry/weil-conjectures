/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantDerivedDirectImage
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.RingTheory.Flat.CategoryTheory
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaArrows
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.Algebra.Homology.CanonicalRingedTensorComparison.RingedTopoiCanonicalTensorPullbackSupplement
import Mathlib.Algebra.Homology.BifunctorShift
public import WeilConjectures.AlgebraicGeometry.RingedProjectionRestrictionData

/-!
# Canonical localization comparisons for the projection mate

Source: Stacks Project, Cohomology on Sites, Tags 08FI, 0FN5, 07A4 and 0B56;
Modules on Sites, Tag 04J0 (blueprint: lem-weil-pbc-ringed-projection-restriction).

All model functors below carry natural representative comparisons. Ordinary operations
are Mathlib's module pullback and pushforward for the specified ring map. Tensor
comparisons are normalized on pure tensors and signed total complexes; derived
adjunctions are normalized by the ordinary counit on K-injectives. No operation or
projection arrow is selected from an unconstrained existence statement.

## Main definitions

* `ProjectionRestriction.Operation`: the canonical module and derived operations.
* `ProjectionRestriction.TensorModel`: derived tensor normalized on resolving pairs.
* `ProjectionRestriction.Local`: canonical slice comparisons and their normalizations.

The assembly theorem `ringedProjectionRestriction` is in
`WeilConjectures.AlgebraicGeometry.Ringed.RingedProjectionRestriction`.
This module contains its unchanged data
interfaces so the construction lemmas can be imported without a cycle.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option backward.isDefEq.respectTransparency true
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open AlgebraicGeometry

namespace AlgebraicGeometry.Scheme.ProjectionRestriction

variable {C D : Type (u + 1)} [Category.{u} C] [Category.{u} D]
  [EssentiallySmall.{u + 1} C] [EssentiallySmall.{u + 1} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}

attribute [instance_reducible, instance] TensorShifts.shifts

attribute [instance] Operation.rightAdjoint Operation.pullbackAdditive
  Operation.pushforwardAdditive Operation.pullbackLimits Operation.pullbackColimits

namespace Operation

variable {F : C ⥤ D} {R : Sheaf J CommRingCat.{u + 1}}
  {S : Sheaf K CommRingCat.{u + 1}} (o : Operation F R S)

end Operation

namespace Operation

end Operation

end AlgebraicGeometry.Scheme.ProjectionRestriction

namespace AlgebraicGeometry.Scheme.ProjectionRestriction
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R_Y : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (R_X : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R_Y ≅ R_X)

end AlgebraicGeometry.Scheme.ProjectionRestriction
