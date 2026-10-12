/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group P3
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Triangulated.Subcategory

/-! # Triangulated closure of supported quasi-coherent complexes

Source: Stacks Project, Tag 0A9A, preceding definition of D_QCoh,T.
(blueprint: lem-pc-supported-qcoh-triangulated).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

/-- Quasi-coherent cohomology with zero stalks off T is stable under triangles.
No compactness or closedness assumption on T is needed for this closure assertion.
Source: Stacks Project, Derived Categories of Schemes, definition preceding Tag 0A9A.
(blueprint: lem-pc-supported-qcoh-triangulated).

Proof:
1. The zero complex has zero cohomology sheaves; these are quasi-coherent and their
   stalks are zero. This verifies ContainsZero.
2. Cohomology of K shifted by m is canonically cohomology of K in degree n+m.
   Quasi-coherence and zero stalks are invariant under these isomorphisms. This verifies
   IsStableUnderShift for every integer shift, including negative shifts.
3. Apply cohomology to a distinguished triangle with its first and third objects in
   the property. Its middle cohomology sheaf is an extension of a cokernel between
   quasi-coherent cohomology sheaves and a kernel between such sheaves. Kernels,
   cokernels and extensions of quasi-coherent modules on a scheme are quasi-coherent,
   as can be checked on affine opens by the exact module-to-sheaf equivalence.
4. At a point outside T, stalks preserve exact sequences. The long exact cohomology
   sequence has zero terms on both sides of each middle term, so that term is zero.
   Consequently the middle object has the property itself, hence also its isoClosure.
   These three assertions give ObjectProperty.IsTriangulated. The empty subset and
   the whole space require exactly the same argument. -/
theorem supported_qcoh_isTriangulated (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (T : Set X) :
    ObjectProperty.IsTriangulated (fun K : schemeDerivedCategory X ↦
      schemeDerivedQCohProperty X K ∧
        ∀ (n : ℤ) (x : X), x ∉ T →
          Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x))) := by
  sorry

end AlgebraicGeometry
