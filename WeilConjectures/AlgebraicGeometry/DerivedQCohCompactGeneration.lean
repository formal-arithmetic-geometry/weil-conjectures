/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.CategoryTheory.CompactlyGenerated
public import Mathlib.CategoryTheory.Triangulated.Subcategory
public import Mathlib.Topology.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.DerivedQCohPerfectGeneration
import WeilConjectures.AlgebraicGeometry.PerfectComplexRepresentatives
import WeilConjectures.AlgebraicGeometry.PerfectObjectCompact
import WeilConjectures.AlgebraicGeometry.DerivedOpenLocalization
import WeilConjectures.AlgebraicGeometry.SupportedPerfectGenerator
import WeilConjectures.AlgebraicGeometry.DerivedQCohCompactGenerationCore

/-! # Compact generation of the quasi-coherent derived category

Source: Stacks Project, Derived Categories of Schemes, Theorem 36.15.3 (Tag 09IS),
and Derived Categories, Definition 13.37.5 (Tag 09SQ).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- For a quasi-compact quasi-separated scheme, the full subcategory of complexes with
quasi-coherent cohomology is compactly generated, with its inherited triangulated structure
(Stacks, Tags 09IS and 09SQ). -/
theorem schemeDerivedQCoh_compactlyGenerated (X : Scheme.{u})
    [CompactSpace X] [QuasiSeparatedSpace X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))] :
    ∃ htri : (schemeDerivedQCohProperty X).IsTriangulated,
      letI := htri
      ∃ hsums : HasCoproducts.{u} (schemeDerivedQCohCategory X),
        letI := hsums
        IsCompactlyGeneratedTriangulated.{u} (schemeDerivedQCohCategory X) := by
  let := Classical.choice (nonempty_derivedOpenLocalization X)
  have htri : (schemeDerivedQCohProperty X).IsTriangulated := by
    have hs := (supported_perfect_generator X Set.univ isClosed_univ (by simp)).1
    simpa using hs
  refine ⟨htri, ?_⟩
  let := htri
  let := derivedQCohDirectSums X
  obtain ⟨I, P, hperfect, hrepresentatives⟩ := Scheme.exists_perfectComplex_representatives X
  refine ⟨derivedQCohDirectSums X, I, P, ?_, ?_⟩
  · exact fun i ↦ perfectObjectCompact X (P i) (hperfect i)
  · exact schemeDerivedQCoh_representatives_generate X htri P hrepresentatives
      (derivedQCohPerfectGeneration X)

end AlgebraicGeometry
