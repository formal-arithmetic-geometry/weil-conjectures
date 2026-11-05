/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Projection.ProjectionFormulaBaseChangeNaturality
public import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionGlobalModel
import WeilConjectures.AlgebraicGeometry.ProEtale.Projection.ProEtaleProjectionGlobalComparison
import WeilConjectures.AlgebraicGeometry.ProjectionRestriction.RingedProjectionTensorExact
import WeilConjectures.AlgebraicGeometry.SignedProjectionResolution.SignedProjectionResolutionNormalization
import Mathlib.CategoryTheory.Triangulated.Adjunction

/-!
# Natural transformation and unit normalization of the pro-etale projection mate

Source: Stacks, Cohomology on Sites, Tags 06YU, 07A4, 07A6 and 0B56.
(blueprint: lem-weil-pbc-proetale-projection-mate-data-s4).

The shifts are constructed together with the mate, by transport from the normalized
model. Arbitrary independently chosen shift structures do not suffice.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [local instance 100] HasDerivedCategory.standard
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
variable {X Y : Scheme.{u}} (f : X ⟶ Y)
  (R : Sheaf (ProEt.topology Y) CommRingCat.{u + 1})
  (S : Sheaf (ProEt.topology X) CommRingCat.{u + 1})
  (c : (proEtaleSheafInverseImage f CommRingCat.{u + 1}).obj R ≅ S)
  (a : ProEtaleTensorModel Y R) (b : ProEtaleTensorModel X S)
  (E : DerivedCategory (proEtaleRingModules X S))

end AlgebraicGeometry.Scheme
