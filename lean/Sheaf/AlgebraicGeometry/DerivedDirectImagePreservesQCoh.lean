/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group S1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated

/-! # Derived direct image preserves quasi-coherent cohomology

Source: literature/stacks-project/perfect.tex, Tag 08D5,
part (1) (blueprint: lem-pc-derived-direct-image-preserves-qcoh).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- For a quasi-compact and quasi-separated morphism of schemes, derived direct image
preserves the full subcategory of complexes with quasi-coherent cohomology.
Source: literature/stacks-project/perfect.tex, Tag 08D5,
part (1) (blueprint: lem-pc-derived-direct-image-preserves-qcoh).
Proof:
1. Fix an affine open `V` of the target. Restriction of a K-injective resolution to
   `f⁻¹(V)` is K-injective by `lem-sc-derived-k-injective-restrict-open`; termwise
   pushforward and exact restriction identify the restricted derived pushforward and its
   cohomology with those for the induced qcqs morphism to `V`. For each integer `q`,
   `lem-pc-derived-direct-image-uniform-truncation-bound` replaces the complex by a
   bounded-below canonical truncation without changing the degree-`q` higher direct image.
   Apply `thm-sp-truncation-e2`: its E₂ terms are higher direct images of the truncated
   cohomology sheaves, which are quasi-coherent by `lem-pc-finite-support-hi`.
2. The spectral sequence gives a finite filtration in total degree `q`. Its associated
   graded pieces are obtained from E₂ by finitely many kernels modulo images; they are
   quasi-coherent by `lem-weil-pbc-quasi-coherent-module-kernel` and
   `lem-weil-pbc-quasi-coherent-module-cokernel-image`. Descending induction through the
   filtration, using `lem-pc-quasi-coherent-extension`, gives quasi-coherence of the
   degree-`q` cohomology. This holds on every affine open of the target and for every
   integer `q`; locality of quasi-coherence gives the stated membership in D_QCoh.
(blueprint: lem-pc-derived-direct-image-preserves-qcoh). -/
theorem schemeDerivedDirectImage_preserves_QCoh
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))] :
    ∀ E : schemeDerivedCategory X,
      schemeDerivedQCohProperty X E →
        schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj E) := by
  sorry

end AlgebraicGeometry
