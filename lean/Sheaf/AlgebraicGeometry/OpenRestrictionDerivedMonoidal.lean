/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group H4
-/
module

public import Sheaf.AlgebraicGeometry.DerivedTensorStructure
import Sheaf.AlgebraicGeometry.OpenRestrictionKFlatModel
import Sheaf.AlgebraicGeometry.OpenRestrictionTotalTensor
import Sheaf.Algebra.Homology.KFlatResolution
import Sheaf.AlgebraicGeometry.OpenRestrictionTensorNaturality
import WeilConjectures.AlgebraicGeometry.Modules.PullbackMonoidal

/-! # Strong monoidal descent of open restriction
Source: Stacks Project, Tags 06YH and 079U.
(blueprint: lem-pc-open-restriction-derived-monoidal).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u w
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
  TopologicalSpace

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Use the standard localization on the open scheme.
Source: Stacks Project, Tag 05RU.
(blueprint: lem-pc-open-restriction-derived-monoidal). -/
local instance openRestrictionMonoidalStandardDerived (X : Scheme.{u}) (U : X.Opens) :
    HasDerivedCategory.{u + 1}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
  HasDerivedCategory.standard _

/-- Strong monoidal descent of exact restriction to the standard category on the open.

Source: Stacks Project, cohomology.tex, Tags 06YH and 079U.
(blueprint: lem-pc-open-restriction-derived-monoidal).

Proof: give ordinary restriction followed by the over-equivalence the monoidal
structure transported from Scheme.Modules.pullbackMonoidal U.ι along
Scheme.Modules.overFunctorEquiv U and restrictFunctorIsoPullback U.ι.
Resolve the two tensor inputs by K-flat complexes. Their restrictions are K-flat
by lem-pc-open-restriction-kflat-model. The ordinary tensorators, summed over
p + q = n, give the total-complex comparison of
lem-pc-open-restriction-total-tensor, natural by
lem-pc-open-restriction-tensor-natural. Localize and use the factorization
isomorphisms of both exact functors to identify their composite with R.
Common K-flat resolutions make these comparisons independent of representatives
and natural for roofs. The tensor unit is the structure sheaf in degree zero;
ordinary restriction identifies it with the structure sheaf on U.toScheme.
The module monoidal structure satisfies associativity and the two unit laws.
On total complexes these equations hold on each coproduct inclusion, with the
same associators and signs; localization preserves the equations. Check them
on K-flat representatives and transport to arbitrary objects by naturality.
The tensor and unit comparisons are invertible, hence give R.Monoidal.
Localization's universal property applies separately to the source, over-site,
and standard open-scheme localizations, so no equality of their morphism
universes is required. For the empty open the module and complex comparisons
are between zero objects; zero inputs also satisfy these equations. -/
theorem exists_openRestriction_derivedMonoidal (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    let E := (Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)).mapDerivedCategory
    let R := (SheafOfModules.overFunctor.{u}
      (moduleRings X.toRingedSpace) U).mapDerivedCategory ⋙ E
    Nonempty R.Monoidal := by sorry

end AlgebraicGeometry
