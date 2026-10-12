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

import Sheaf.AlgebraicGeometry.DerivedAmbientDirectSums
import Sheaf.AlgebraicGeometry.Modules.QuasicoherentBinarySum
import Sheaf.AlgebraicGeometry.QuasiCoherentModuleColimitAffineSections
import Sheaf.CategoryTheory.TruncationHypercohomology
import Sheaf.AlgebraicGeometry.QcqsCohomologyDirectSum
import Sheaf.Paper.HigherDirectImagePresheaf
import Sheaf.AlgebraicGeometry.ModuleSheavesColimitsForgetful

/-! # The uniformly lower-truncated coproduct comparison

Source: Stacks Project, Tags 08DZ and 015J
(blueprint: lem-pc-derived-direct-image-truncated-coproduct).
-/

@[expose] public section

universe u₁ w₁ w₂

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- After a single common lower truncation, derived direct-image cohomology commutes
with an ambient coproduct of objects with quasi-coherent cohomology.
Source: Stacks Project, Tag 08DZ, bounded-below comparison, and Tag 015J
(blueprint: lem-pc-derived-direct-image-truncated-coproduct).

Proof. Exact sums in module sheaves identify the cohomology of the ambient coproduct
with the sums of the summands' cohomology. Quasi-coherence is preserved by sums:
write the sum as the directed colimit of finite sums, including the empty finite sum,
and use the affine-section colimit theorem. Exact sums also commute with the canonical
lower truncation. Hence the truncated cofan is a coproduct with quasi-coherent cohomology
and common lower bound a. Apply the natural truncation hypercohomology spectral sequence
for direct image to this cofan. Its E₂ terms are R^p f_* H^r. On affine opens of Y,
their presheaf descriptions are cohomology on qcqs inverse images. Qcqs cohomology
commutes with sums; sheafification of module presheaves preserves sums. Thus the E₂
comparison is an isomorphism. Exact sums commute with the kernels and images defining
successive pages, so all page comparisons are isomorphisms. In degree q the range
0 ≤ p ≤ q-a is finite. The convergent filtrations therefore have isomorphic graded
pieces; induction on their short exact sequences makes the abutment comparison an
isomorphism. Naturality identifies it with the displayed map. For q<a the abutments
vanish, and the empty family is covered by exactness and the zero coproduct. -/
theorem derivedDirectImage_truncated_cohomology_coproduct
    {X Y : Scheme.{u₁}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₂} (SheafOfModules.{u₁} (moduleRings Y.toRingedSpace))]
    (I : Type u₁) (E : I → schemeDerivedQCohCategory X)
    (S : schemeDerivedCategory X) (ι : ∀ i, (E i).obj ⟶ S)
    (hc : IsColimit (Cofan.mk S ι)) (a q : ℤ) :
    IsIso (Sigma.desc (fun i ↦ (schemeHigherDirectImage f q).map
      ((DerivedCategory.TStructure.t.truncGE a).map (ι i)))) := by
  sorry

end AlgebraicGeometry
