/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group B3
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import Mathlib.CategoryTheory.Limits.Shapes.Products

public import Mathlib.Algebra.DirectSum.Module

import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import Sheaf.CategoryTheory.ExactCoupleMorphism
import Sheaf.CategoryTheory.FiniteFiltrationInduction
import Sheaf.CategoryTheory.TruncationHypercohomology
import Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum
import Sheaf.Paper.HigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import Sheaf.AlgebraicGeometry.Modules.QuasiCoherentCokernelImage
import Sheaf.AlgebraicGeometry.Modules.QuasicoherentExtension

/-! # Finite-support representatives of truncated direct-image cohomology

Source: Stacks Project, Tags 08DZ and 015J
(blueprint: lem-pc-truncated-direct-image-affine-finite-support).
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

open Classical in
/-- On an affine open, every section of truncated direct-image cohomology of an
ambient coproduct comes from finitely many summands.
Source: Stacks Project, Tag 08DZ, bounded-below spectral-sequence argument, and Tag 015J
(blueprint: lem-pc-truncated-direct-image-affine-finite-support).

Proof. Choose termwise representatives of the ambient coproduct. Exact sums compute
its cohomology as the sum of the summands' cohomology, and these sums are quasi-coherent.
Exact sums commute with lower truncation, so the truncated family and its coproduct
have the common lower bound a. Over an affine open U of Y, the inverse image is qcqs.
The natural bounded-below hypercohomology spectral sequences have second pages
H^p(f⁻¹U,H^r(τ≥a E)). Cohomology of module sheaves on this qcqs inverse image commutes
with sums. Thus the second-page comparison is bijective. Exact sums commute with the
kernels and images of differentials, so all page comparisons are bijective. In total
degree q there are only the finitely many indices 0 ≤ p ≤ q-a. The finite convergent
filtrations therefore give surjectivity on the abutment: lift a section of the top
nonzero graded piece, subtract its image, and repeat in the next filtration step.
Each lift has finite support; the union of the finitely many supports is finite.
To justify quasi-coherence of the second-page terms, on an affine open V of Y
localize at a section t of O_Y(V). Cohomology of a quasi-coherent module on the qcqs
preimage of V commutes with localization at f*t: prove this from affine acyclicity
and localization of sections, then glue finite affine covers by Mayer--Vietoris,
using quasi-separatedness for quasi-compact overlaps. The resulting identifications
are compatible with restriction to principal opens of V. The higher-direct-image
presheaf description therefore gives quasi-coherent second-page sheaves.
Kernel and cokernel closure propagate quasi-coherence to all later pages. The finite
convergent filtration expresses the abutment as successive extensions of these
quasi-coherent stable page terms, starting at zero, so its cohomology is quasi-coherent.
Consequently, exact sections on the affine open U identify the sheaf abutments with
the displayed section modules. Naturality identifies the map with the displayed
linear map. If q<a the target is zero. If I is empty the ambient coproduct and its
lower truncation are zero, so the target is zero as well. -/
theorem truncated_directImage_affine_finiteSupport
    {X Y : Scheme.{u₁}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a q : ℤ) (U : Y.Opens) (hU : IsAffineOpen U) :
    Function.Surjective
      (DirectSum.toModule ((moduleRings Y.toRingedSpace).obj.obj (op U)) I
        (((SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)).obj
          ((schemeHigherDirectImage f q).obj
            ((DerivedCategory.TStructure.t.truncGE a).obj S))))
        (fun i ↦ ((SheafOfModules.evaluation (moduleRings Y.toRingedSpace) (op U)).map
          ((schemeHigherDirectImage f q).map
            ((DerivedCategory.TStructure.t.truncGE a).map (ι i)))).hom)) := by
  sorry

end AlgebraicGeometry
