/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedPullback
public import Sheaf.Algebra.Homology.KFlat
import Sheaf.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence

/-! # Affine-local cohomology of derived tensor

Source: Stacks Project, Tag 08DX, part (1), with its affine calculation in part (2).
(blueprint: lem-pc-derived-tensor-qcoh-component).
-/

@[expose] public section

universe uX wD

open CategoryTheory MonoidalCategory

namespace AlgebraicGeometry

noncomputable local instance (X : Scheme.{uX}) :
    MonoidalCategory (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) :=
  SheafOfModules.monoidalCategory X.sheaf

set_option synthInstance.maxSize 256 in
/-- Affine-local cohomology calculation for a K-flat tensor representative.
Source: Stacks Project, Tag 08DX(1), proof using Tag 08DX(2) and Tag 06Z0.
Proof: exact restriction commutes with cohomology and with the total tensor of complexes,
and preserves K-flatness. On the affine U, represent the restrictions of Q(P) and Q(N)
by tilde of module complexes using 06Z0. Resolve the first module complex by a K-flat
complex. The affine tensor comparison identifies the restricted tensor representative
with tilde of the total tensor of this resolution and the second module complex.
Tilde is exact, so every cohomology sheaf is tilde of a module and is quasi-coherent.
Transfer through the derived comparison and the equivalence with the over category.
This works in all degrees, including unbounded complexes and the empty open.
(blueprint: lem-pc-derived-tensor-qcoh-component). -/
theorem derivedTensor_cohomology_over_affine {X : Scheme.{uX}}
    [HasDerivedCategory.{wD} (SheafOfModules.{uX} (moduleRings X.toRingedSpace))]
    (P N : CochainComplex (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) ℤ)
    (hP : CochainComplex.IsKFlat (R := X.sheaf) P)
    (hPQ : schemeDerivedQCohProperty X (DerivedCategory.Q.obj P))
    (hNQ : schemeDerivedQCohProperty X (DerivedCategory.Q.obj N))
    (n : ℤ) (U : X.Opens) (hU : IsAffineOpen U) :
    (((DerivedCategory.homologyFunctor
      (SheafOfModules.{uX} (moduleRings X.toRingedSpace)) n).obj
        (DerivedCategory.Q.obj
          (CochainComplex.mapBifunctor P N (curriedTensor _)))).over U).IsQuasicoherent := by
  sorry

end AlgebraicGeometry
