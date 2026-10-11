/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Right adjoint to derived direct image on quasi-coherent complexes

Source: Stacks Project, Duality for Schemes, Lemma 48.3.1 (Tag 0A9E)
(blueprint: lem-pc-qcqs-derived-direct-image-right-adjoint).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- For a qcqs morphism between qcqs schemes, derived direct image preserves quasi-coherent
cohomology, and its restriction to the full quasi-coherent derived categories has a right
adjoint. Source: Stacks Project, Lemma 48.3.1 (Tag 0A9E)
(blueprint: lem-pc-qcqs-derived-direct-image-right-adjoint).

Proof:
1. By `lem-pc-derived-direct-image-preserves-qcoh` (Tag 08D5 (1)), the qcqs morphism
sends complexes with quasi-coherent cohomology to complexes with quasi-coherent cohomology.
This supplies the witness `hpres` and makes the full-subcategory lift well defined.
2. By `lem-pc-derived-qcoh-direct-sums`, both quasi-coherent derived categories have all
set-indexed direct sums.
3. By `lem-pc-derived-qcoh-compact-generation`, the source category is compactly generated,
since X is quasi-compact and quasi-separated.
4. By `lem-pc-derived-direct-image-preserves-direct-sums`, the restricted derived direct
image commutes with all set-indexed direct sums, since f is qcqs.
5. The derived category and derived direct image definitions (`def-pc-derived-category`,
`def-pc-derived-direct-image`), together with `lem-pc-right-derived-functor-triangulated`,
make this restriction exact as a functor of triangulated categories. Apply
`lem-pc-brown-representability-right-adjoint` using Steps 2, 3 and 4 to obtain a right adjoint.
-/
theorem schemeDerivedDirectImage_qcqs_hasRightAdjoint (X Y : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f] :
    ∃ hpres : ∀ E : schemeDerivedCategory X, schemeDerivedQCohProperty X E →
        schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E),
      ((schemeDerivedQCohProperty Y).lift
        ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f)
        (fun E ↦ hpres E.obj E.property)).IsLeftAdjoint := by
  sorry

end AlgebraicGeometry
