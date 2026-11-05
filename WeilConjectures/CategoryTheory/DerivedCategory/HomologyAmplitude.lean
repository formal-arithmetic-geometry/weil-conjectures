/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# Upper amplitude bounds of triangulated functors between derived categories

Let `F : D(A) ⥤ D(B)` be a triangulated functor whose values on objects of `A` (placed in
degree `0`) have homology only in degrees `≤ e`. Then for an object `K` with homology in degrees
`[a, b]`, `F K` has homology only in degrees `≤ b + e`
(`DerivedCategory.isZero_homology_obj_of_isGE_of_isLE`). This is the spectral-sequence-free
form of the estimate "the `E₂^{p,q}`-terms vanish for `p > e`, so unbounded degrees can only enter
through `q`" of blueprints `rem-sf-fullcd-reduction` (3) and `rem-sf-fullcd-general-form` (a).
The proof is by induction on `b - a`, splitting `K` by the truncation triangle
`τ_{< b} K ⟶ K ⟶ τ_{≥ b} K` and using the long exact homology sequence.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

namespace DerivedCategory

variable {A B : Type*} [Category* A] [Abelian A] [HasDerivedCategory A] [Category* B] [Abelian B]
  [HasDerivedCategory B] (F : DerivedCategory A ⥤ DerivedCategory B) [F.CommShift ℤ]
  [F.IsTriangulated]

end DerivedCategory
