/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.Algebra.Homology.KFlatStalkCriterion

/-! # K-flat models under open restriction

Source: Stacks Project, Tag 08DX, proof of (1).
(blueprint: lem-pc-open-restriction-kflat-model).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits MonoidalCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- The recorded sheaf tensor, used for total complexes. Source: Stacks, Tag 06Y7
(blueprint: lem-pc-open-restriction-kflat-model). -/
noncomputable local instance openRestrictionKFlatModelTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Open restriction preserves K-flatness for the canonical over-site restriction.
Source: Stacks Project, Tag 06YC, specialized to the open inclusion; Tag 08DX(1).
Proof: K-flatness is detected on stalks (Tag 06YB). For a point x of U, the
stalk ring and stalk module of the restricted sheaf identify with the corresponding
stalks at the image of x in X. The cofinal neighborhoods contained in U induce these
identifications; they are natural in module maps, so they also identify differentials
of the stalk complexes. Transport tensor products and acyclicity through the stalk-ring
isomorphism. K-flatness of P supplies the stalkwise K-flatness on X, hence that of its
restriction on U. Apply the stalk criterion on U to conclude. No condition on the
terms or boundedness is used. For the empty open the stalk condition is vacuous.
(blueprint: lem-pc-open-restriction-kflat-model). -/
theorem openRestriction_isKFlat (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P) :
    let R :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)
    CochainComplex.IsKFlat (R := U.toScheme.sheaf)
      ((R.mapHomologicalComplex (.up ℤ)).obj P) := by
  sorry

end AlgebraicGeometry
