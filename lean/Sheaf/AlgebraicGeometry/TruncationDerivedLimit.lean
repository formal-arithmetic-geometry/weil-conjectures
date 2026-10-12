/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group U1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Sheaf.Topology.OpenModuleCohomology
public import Sheaf.CategoryTheory.Triangulated.DerivedLimit
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence
import Sheaf.CategoryTheory.Triangulated.RingedSpaceDerivedProducts
import Sheaf.Topology.PointwiseTruncationLimit

/-! # Reconstruction from lower truncations under a local cohomological bound

Source: Stacks Project, Cohomology of Sheaves, Tag 0D64, specialized to a scheme
(blueprint: lem-pc-ringed-space-truncation-derived-limit).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- A uniform cohomological bound on a basis for the negative cohomology sheaves
exhibits a complex as the derived limit of its standard lower truncations.
Source: Stacks Project, Tag 0D64
(blueprint: lem-pc-ringed-space-truncation-derived-limit).

Proof:
1. For each point x use the basis opens containing x as a fundamental system of
neighborhoods. Put p_x(m) = d + max(0,m). If p > p_x(m) and m-p < 0, the assumed
vanishing applies since p > d. If m-p >= 0, then p <= m <= max(0,m)+d, a contradiction.
Thus lem-pc-ringed-space-pointwise-truncation-limit applies.
2. By lem-pc-ringed-space-derived-products the product of the truncations exists.
By lem-weil-derived-limit-existence (1), choose a derived limit (K,p_K,delta_K).
The pointwise criterion supplies an isomorphism c : E -> K whose composite with each
product projection is the canonical truncation map.
3. Transport the distinguished Roos triangle along c (def-weil-triangulated-category).
Its first map p_K composed with c is the product lift of the canonical truncation maps,
and its last map is delta_K followed by the shifted inverse of c. This gives precisely
the specified IsDerivedLimitTriangle (def-weil-derived-limit), hence the canonical
comparison with the chosen derived limit is an isomorphism. -/
theorem truncation_isDerivedLimitTriangle_of_local_bound (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hE : ∃ (d : ℕ) (B : Set (Opens X)),
      IsTopologicalBasis ((fun U : Opens X => (U : Set X)) '' B) ∧
      ∀ (U : Opens X), U ∈ B → ∀ (p : ℕ), d < p → ∀ (q : ℤ), q < 0 →
        IsZero ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (moduleRings X.toRingedSpace)) q).obj E))) :
    ∃ (_ : HasProduct (fun n : ℕ => ((DerivedCategory.TStructure.t
        (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).truncGE (-(n : ℤ))).obj E)),
      ∃ δ : (∏ᶜ (fun n : ℕ => ((DerivedCategory.TStructure.t
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).truncGE
            (-(n : ℤ))).obj E)) ⟶ E⟦(1 : ℤ)⟧,
        IsDerivedLimitTriangle (fun n : ℕ => ((DerivedCategory.TStructure.t
          (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).natTransTruncGEOfLE
            (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) (by omega)).app E) E
          (Pi.lift (fun n : ℕ => ((DerivedCategory.TStructure.t
            (C := SheafOfModules.{u} (moduleRings X.toRingedSpace))).truncGEπ
              (-(n : ℤ))).app E)) δ := by
  sorry

end AlgebraicGeometry
