/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group Y2
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.KFlat

/-! # Open restriction of total tensor complexes

Source: Stacks Project, Tag 08DX, proof of (1).
(blueprint: lem-pc-open-restriction-total-tensor).
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
(blueprint: lem-pc-open-restriction-total-tensor). -/
noncomputable local instance openRestrictionTotalTensorTensor (X : Scheme.{u}) :
    MonoidalCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

/-- Restriction commutes with the signed direct-sum total tensor of arbitrary complexes.
Source: Stacks Project, Tag 08DX, proof of (1); Tag 01CD for the sheaf tensor comparison.
Proof: the restriction tensor comparison identifies the tensor of restricted terms
with restriction of the tensor in every bidegree. It is natural in both terms:
the comparison on pure tensors commutes with restriction of either module map.
Restriction preserves arbitrary coproducts, so summing these comparisons over
p + q = n gives an isomorphism in each total degree n. Naturality intertwines
both differentials; additivity intertwines the sign (-1)^p in the second one.
The degreewise isomorphisms and their inverses thus define inverse complex maps.
The over equivalence transports the same calculation to modules on U.toScheme.
No boundedness is used; the empty open and zero complexes give the zero comparison.
(blueprint: lem-pc-open-restriction-total-tensor). -/
theorem openRestriction_totalTensor_iso (X : Scheme.{u}) (U : X.Opens)
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    let R :=
    SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U ⋙
      Equivalence.functor
        (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
        (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
        (Scheme.Modules.overEquiv U)
    Nonempty
      ((R.mapHomologicalComplex (.up ℤ)).obj
        (CochainComplex.mapBifunctor P N
          (curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)))) ≅
        CochainComplex.mapBifunctor
          ((R.mapHomologicalComplex (.up ℤ)).obj P)
          ((R.mapHomologicalComplex (.up ℤ)).obj N)
          (curriedTensor (SheafOfModules.{u}
            (moduleRings U.toScheme.toRingedSpace)))) := by
  sorry

end AlgebraicGeometry
