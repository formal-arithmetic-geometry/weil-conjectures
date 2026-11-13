/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.AlgebraicGeometry.UniformDirectImageBoundCore
import WeilConjectures.AlgebraicGeometry.DirectImageTruncationTailBound
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-! # Uniform truncation bound for derived direct image

Source: Stacks Project, Tag 08D5, part (2) and the final truncation argument.
-/

@[expose] public section

universe u wX wS

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a quasi-compact, quasi-separated morphism to a quasi-compact scheme, the
unbounded derived direct image has a uniform upper cohomological bound on objects of
`D_QCoh(𝒪_X)` with no positive cohomology. For every such derived object without the
upper-bound restriction, the canonical map to its sufficiently low lower truncation
induces an isomorphism on any fixed cohomology sheaf after derived direct image
(Stacks, Tag 08D5). -/
theorem exists_schemeDerivedDirectImage_uniform_truncation_bound
    {X S : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wS} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    (f : X ⟶ S) [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    (∃ N : ℤ, 0 < N ∧
      ∀ E : schemeDerivedQCohCategory X,
        (∀ m : ℤ, 0 < m → IsZero
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) m).obj E.obj)) →
        ∀ m : ℤ, N ≤ m → IsZero ((schemeHigherDirectImage f m).obj E.obj)) ∧
    (∀ (E : schemeDerivedQCohCategory X) (q : ℤ),
      ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
        IsIso ((schemeHigherDirectImage f q).map
          ((DerivedCategory.TStructure.t.truncGEπ (-n)).app E.obj))) := by
  obtain ⟨N, hpos, hN⟩ := uniform_bound_core f
  refine ⟨⟨N, hpos, hN⟩, ?_⟩
  intro E q
  refine ⟨N - q, ?_⟩
  intro n hn
  let T := (schemeDerivedDirectImage f).mapTriangle.obj
    ((DerivedCategory.TStructure.t.triangleLTGE (-n)).obj E.obj)
  have hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
    (schemeDerivedDirectImage f).map_distinguished _
      (DerivedCategory.TStructure.t.triangleLTGE_distinguished (-n) E.obj)
  have hz : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).obj T.obj₁) :=
    directImage_truncation_tail_bound f N hN E n q (by omega)
  have hz' : IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings S.toRingedSpace)) (q + 1)).obj T.obj₁) :=
    directImage_truncation_tail_bound f N hN E n (q + 1) (by omega)
  change IsIso ((DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings S.toRingedSpace)) q).map T.mor₂)
  exact DerivedCategory.isIso_homologyMap_mor₂ T hT q (q + 1) rfl hz hz'

end AlgebraicGeometry
