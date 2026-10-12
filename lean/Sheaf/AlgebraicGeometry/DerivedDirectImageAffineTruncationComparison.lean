/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group R1
-/
module

public import Sheaf.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Sheaf.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import Sheaf.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # Local truncation comparison for unbounded direct image

Source: Stacks Project, perfect.tex, Tag 08D5, final paragraph
(blueprint: lem-pc-derived-direct-image-affine-truncation-comparison).
-/

@[expose] public section

universe u wX wY

open CategoryTheory

namespace AlgebraicGeometry

/-- On an affine open, a sufficiently low canonical truncation induces an
isomorphism on any fixed higher direct image. The assertion concerns the actual
canonical map, and does not assert quasi-coherence of either higher direct image.
Source: Stacks Project, perfect.tex, Tag 08D5, final paragraph; cohomology.tex,
Tag 08BS for open restriction
(blueprint: lem-pc-derived-direct-image-affine-truncation-comparison).

Proof:
1. Put V = f^-1(U). The induced morphism V -> U is qcqs, by base change along
   the open immersion U -> Y. The affine scheme U is quasi-compact.
2. Exact restriction of E to V has quasi-coherent cohomology. Choose a
   K-injective representative of E; kInjective_of_restrict_open says that
   its restriction is K-injective. Use schemeDerivedDirectImage_openRestriction
   to identify the restriction of Rf_*E with R(f|V)_*(E|V), naturally in E.
3. Apply exists_schemeDerivedDirectImage_uniform_truncation_bound, its second
   clause, to V -> U, E|V and q, and choose n at least the resulting n0.
   This makes the q-th higher direct image of the truncation projection an iso.
4. Exact restriction commutes with canonical truncation and its projection,
   by the standard t-structure, and with homology. Transport the iso of step 3
   through these natural comparisons. It is precisely the displayed map.
-/
theorem exists_isIso_schemeHigherDirectImage_truncGE_over_affine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (q : ℤ) (U : Y.affineOpens) :
    ∃ n : ℤ, IsIso
      ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U.1).map
        ((schemeHigherDirectImage f q).map
          ((DerivedCategory.TStructure.t.truncGEπ (-n)).app E))) := by sorry

end AlgebraicGeometry
