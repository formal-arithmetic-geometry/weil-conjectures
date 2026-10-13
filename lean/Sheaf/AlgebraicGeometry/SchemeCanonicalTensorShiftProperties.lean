/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group G1
-/
module

public import Sheaf.Algebra.Homology.KFlat
public import Mathlib.CategoryTheory.Triangulated.Functor

public import Sheaf.AlgebraicGeometry.SchemeCanonicalTensorShift
/-! # Exactness and unitality of canonical tensor shifts
Source: Stacks Project, Tag 06YH and the Koszul unitor identity.
(blueprint: lem-sc-scheme-canonical-tensor-shift-properties).
-/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits MonoidalCategory
namespace AlgebraicGeometry
/-- Canonical tensor shifts are exact and their degree-one right-unitor squares hold.
Source: Stacks Tag 06YH; total-complex shift/unitor calculation used in Tag 08EU.
(blueprint: lem-sc-scheme-canonical-tensor-shift-properties).

Proof. For a fixed K-flat complex the canonical shift comparison agrees with the
comparison descended from tensoring mapping-cone triangles on the homotopy category.
The tensor functor is therefore exact. A K-flat replacement of the fixed factor and
naturality of the two-variable shift comparison transport this to every fixed object.
For the unitor square, use the bifunctor localization comparison with the unit fixed
in the second factor and a K-flat complex P in the first. Expand the comparison's
shift square. The complex right unitor satisfies the Koszul translation identity in
every degree. Naturality of the unitor absorbs the inclusion's shift map. Cancel the
invertible localization shift comparison to obtain the square at Q(P). The identity
functor has its standard shift. Zero factors and the empty scheme give zero maps. -/
theorem schemeCanonicalTensorShift_properties (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    letI := schemeCanonicalTensorShift Y
    letI : ∀ M : schemeDerivedCategory Y, (tensorRight M).CommShift ℤ :=
      fun M => Functor.CommShift₂.commShiftFlipObj (h := .int) M
    (∀ M : schemeDerivedCategory Y, (tensorRight M).IsTriangulated) ∧
      (∀ P : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
        CochainComplex.IsKFlat (R := Y.sheaf) P →
        let K := DerivedCategory.Q.obj P
        let τ := (rightUnitorNatIso (schemeDerivedCategory Y)).hom
        ((tensorRight (𝟙_ (schemeDerivedCategory Y))).commShiftIso (1 : ℤ)).hom.app K ≫
            (τ.app K)⟦(1 : ℤ)⟧' =
          τ.app (K⟦(1 : ℤ)⟧) ≫ ((𝟭 (schemeDerivedCategory Y)).commShiftIso
            (1 : ℤ)).hom.app K) := by sorry

end AlgebraicGeometry
