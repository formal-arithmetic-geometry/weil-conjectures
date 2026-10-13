/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.Algebra.Homology.KFlat

/-! # Comparison with prescribed local strictly perfect tensor models

Source: Stacks Project, Cohomology of Sheaves, Tags 09J5 and 06YH; Schemes,
Tag 08DX (blueprint: lem-sc-strict-perfect-tensor-local-comparison).
-/

@[expose] public section

universe u w

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory

set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

local instance sptc_globalTensorZero (X : Scheme.{u}) :
    (@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor X.sheaf

local instance sptc_globalTensorObjZero (X : Scheme.{u})
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    ((@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj X.sheaf M

local instance sptc_localTensorZero (X : Scheme.{u}) (U : X.Opens) :
    (@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor (X.sheaf.over U)

local instance sptc_localTensorObjZero (X : Scheme.{u}) (U : X.Opens)
    (M : SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :
    ((@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))).obj M).PreservesZeroMorphisms :=
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj (X.sheaf.over U) M

local instance sptc_globalColimits (X : Scheme.{u}) :
    CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) := inferInstance

local instance sptc_localColimits (X : Scheme.{u}) (U : X.Opens) :
    CategoryTheory.Limits.HasColimitsOfSize.{0, 0}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) := inferInstance

local instance sptc_globalTotal (X : Scheme.{u})
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ) :
    HomologicalComplex.HasMapBifunctor P N
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory X.sheaf)) (.up ℤ) :=
  fun _ ↦ inferInstance

local instance sptc_localTotal (X : Scheme.{u}) (U : X.Opens)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor A B
      (@curriedTensor _ _ (SheafOfModules.monoidalCategory (X.sheaf.over U))) (.up ℤ) :=
  fun _ ↦ inferInstance

set_option maxHeartbeats 800000 in
-- Comparing the localized carrier with its sheaf tensor needs extra elaboration steps.
/-- On a fixed open, prescribed strictly perfect models compute the restriction of the
ordinary tensor of global K-flat representatives. No perfectness hypothesis or choice of
neighbourhood is involved.
Source: Stacks Project, Cohomology of Sheaves, Lemma 09J5, local reduction and K-flat
computation; Tag 06YH, independence of K-flat representatives; Tag 08DX, open restriction.
(blueprint: lem-sc-strict-perfect-tensor-local-comparison).

Proof: Let R be exact restriction to the localized site over U. The comparison between
termwise and derived restriction identifies R(Q(P)) with Q(R(P)), and similarly for N.
Restriction preserves K-flatness, since it is restriction to an open. Restriction also
commutes with sheaf tensor and arbitrary direct sums, so Q(R(Tot(P tensor N))) identifies
with Q(Tot(R(P) tensor R(N))). Each term of A and B is a retract of a finite free sheaf,
hence flat; their upper degree bounds make them K-flat. The K-flat derived tensor
comparison identifies the latter object with Q(R(P)) tensor-derived Q(R(N)). Tensor the
two prescribed derived-category isomorphisms, obtaining Q(A) tensor-derived Q(B).
The same K-flat comparison for A and B identifies this with Q(Tot(A tensor B)). Compose
these isomorphisms. All constructions are on the localized site; no quasi-coherence or
affineness assumption is needed. On the empty open every category object is zero, and
rank-zero free summands and zero complexes obey the same comparison. -/
theorem strictPerfect_tensor_localComparison (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (P N : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hN : CochainComplex.IsKFlat (R := X.sheaf) N)
    (A B : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hA : Scheme.IsStrictlyPerfect X U A) (hB : Scheme.IsStrictlyPerfect X U B)
    (eA : Nonempty ((SheafOfModules.overFunctor
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj (DerivedCategory.Q.obj P) ≅
        DerivedCategory.Q.obj A))
    (eB : Nonempty ((SheafOfModules.overFunctor
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj (DerivedCategory.Q.obj N) ≅
        DerivedCategory.Q.obj B)) :
    Nonempty ((SheafOfModules.overFunctor
      (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj
        (DerivedCategory.Q.obj (CochainComplex.mapBifunctor P N
          (@curriedTensor (SheafOfModules.{u} (moduleRings X.toRingedSpace)) _
            (SheafOfModules.monoidalCategory X.sheaf)))) ≅
      DerivedCategory.Q.obj (CochainComplex.mapBifunctor A B
        (@curriedTensor (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) _
          (SheafOfModules.monoidalCategory (X.sheaf.over U))))) := by sorry

end AlgebraicGeometry
