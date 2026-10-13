/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Algebra.Homology.KFlat

/-! # K-flat tensor models under localized open restriction

Source: Stacks Project, Tags 06YC, 01CD and 08DX.
(blueprint: lem-sc-localized-open-kflat-tensor-restriction).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance loktr_globalTensorZero (X : Scheme.{u}) :
    (@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf

local instance loktr_globalTensorObjZero (X : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    ((@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

local instance loktr_localTensorZero (X : Scheme.{u}) (U : X.Opens) :
    (@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor (X.sheaf.over U)

local instance loktr_localTensorObjZero (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
    ((@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (X.sheaf.over U) M

local instance loktr_globalColimits (X : Scheme.{u}) :
    CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance

local instance loktr_localColimits (X : Scheme.{u}) (U : X.Opens) :
    CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) := inferInstance

local instance loktr_globalTotal (X : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    HomologicalComplex.HasMapBifunctor P N
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)) (.up ℤ) :=
  fun _ ↦ inferInstance

local instance loktr_localTotal (X : Scheme.{u}) (U : X.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor A B
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U))) (.up ℤ) :=
  fun _ ↦ inferInstance

set_option maxHeartbeats 800000 in
-- The localized-site tensor carrier needs additional elaboration steps.
/-- Exact open restriction preserves K-flatness and the total tensor model.
Source: Stacks Project, Tag 06YC for K-flat pullback, Tag 01CD for sheaf tensor
and Tag 08DX for local derived tensor computation.
(blueprint: lem-sc-localized-open-kflat-tensor-restriction).

Proof: identify the localized site over U with the usual open site of U.toScheme.
The exact equivalence on module sheaves identifies restriction with pullback along
U.ι. At every point of U the restricted stalk complex is the original stalk complex;
thus the stalk criterion for K-flatness proves both K-flat assertions (Tag 06YC).
The equivalence also identifies tensor products: on sections send a pure tensor
of restricted sections to the restriction of their tensor. These maps descend
through sheafification, and the inverse is given by the same local pure-tensor
formula. They are natural in each factor. Restriction preserves arbitrary direct
sums, so sum these tensor comparisons over p + q = n in each total degree n.
Naturality commutes with the two differentials and additivity with the sign in
the second differential; hence the degreewise comparisons give a complex
isomorphism from the restricted total tensor to the total tensor of the
restrictions. Apply Q and compose with the exact-functor comparison
R.mapDerivedCategoryFactors. Transport back through the localized-site equivalence.
The assertion uses neither local perfect models nor prescribed derived isomorphisms.
On the empty open the stalk criterion is vacuous and all complexes are zero;
rank-zero modules and zero complexes satisfy the same comparisons. -/
theorem localizedOpen_kFlat_tensor_restriction (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hN : CochainComplex.IsKFlat (R := X.sheaf) N) :
    let R := SheafOfModules.overFunctor (moduleRings X.toRingedSpace) U
    let P' := (R.mapHomologicalComplex (.up ℤ)).obj P
    let N' := (R.mapHomologicalComplex (.up ℤ)).obj N
    CochainComplex.IsKFlat (R := X.sheaf.over U) P' ∧
      CochainComplex.IsKFlat (R := X.sheaf.over U) N' ∧
      Nonempty (R.mapDerivedCategory.obj
        (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)))) ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor P' N'
          (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U))))) := by sorry

end AlgebraicGeometry
