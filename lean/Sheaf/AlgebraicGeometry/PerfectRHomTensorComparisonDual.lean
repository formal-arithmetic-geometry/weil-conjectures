/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group D2
-/
module

public import Sheaf.AlgebraicGeometry.PerfectComplex
public import Sheaf.AlgebraicGeometry.DerivedInternalHomAdjunction

import Sheaf.Paper.DerivedInternalHomRestrictOpen
import Sheaf.AlgebraicGeometry.StrictlyPerfectDerivedInternalHom

/-! The quasi-coherent perfect dual underlying the tensor-Hom comparison. -/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.MonoidalCategory Opposite TopologicalSpace

namespace AlgebraicGeometry

/-- A perfect complex has a quasi-coherent perfect internal dual.
Source: Stacks Project, Cohomology, Tag 08DQ.
Proof: around each point choose a strictly-perfect representative E for K and
refine to an affine neighbourhood. Internal Hom restriction and the strictly-perfect
Hom computation identify RHom(K,O) there with the ordinary dual complex Hom(E,O).
Dualizing a splitting of a finite free term gives a splitting of its dual, so this
complex is strictly perfect and has quasi-coherent terms. Kernels and cokernels of
maps of quasi-coherent sheaves on a scheme are quasi-coherent, so its cohomology
sheaves are quasi-coherent. Quasi-coherence is local on the scheme. Therefore the
actual object RHom(K,O) has quasi-coherent cohomology and satisfies IsPerfect.
Equip that object with its quasi-coherence proof to form D in the full subcategory;
its underlying object is exactly RHom(K,O), rather than an arbitrary existence witness.
(blueprint: lem-pc-perfect-rhom-tensor-comparison-dual) -/
theorem exists_perfect_rhom_dual
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens, HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (K : schemeDerivedQCohCategory X)
    (hK : Scheme.IsPerfect X K.obj) :
    ∃ Kdual : schemeDerivedQCohCategory X,
      Kdual.obj =
        (derivedInternalHom (Opens.grothendieckTopology X.toRingedSpace)
          X.toRingedSpace.sheaf).obj (op K.obj, 𝟙_ (schemeDerivedCategory X)) ∧
      Scheme.IsPerfect X Kdual.obj := by
  sorry

end AlgebraicGeometry
