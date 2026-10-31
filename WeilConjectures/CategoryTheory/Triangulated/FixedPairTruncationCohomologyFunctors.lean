/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.CategoryTheory.Triangulated.TStructure.Homology
public import WeilConjectures.CategoryTheory.Triangulated.CohomologyComparisonPasting

/-! # Shift, truncation and cohomology functors on fixed pairs

Source: BBD, Proposition 1.3.3 and paragraphs 1.3.4--1.3.5, printed pp. 29--31;
canonical fixed-pair transport in steps 2--3 of lem-zl-texact-fixed-pair-heart-cohomology
(blueprint: def-zl-fixed-pair-truncation-cohomology-functors).

The four functors use the existing `IsoAlgebra.mapOfNatIso`. The upper and lower
comparisons are the canonical comparisons used by `truncationCohomologyComparison`.
They are normalized by the truncation counit and unit and require no boundedness.
No triangulated structure on the fixed-pair category is involved.
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u v

namespace CategoryTheory.Triangulated.TStructure

open Limits Endofunctor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- Shift of fixed pairs: `(K, θ)` is sent to `(K[r], θ[r] ∘ s[K,r])`, and a morphism
is sent to its r-shift. The specified coherent shift comparison of P is used.
Source: BBD 1.3.3--1.3.5 and the fixed-pair transport in steps 2--3 of
lem-zl-texact-fixed-pair-heart-cohomology
(blueprint: def-zl-fixed-pair-truncation-cohomology-functors). -/
abbrev fixedPairShift (P : C ⥤ C) [P.CommShift ℤ] (r : ℤ) :
    IsoAlgebra P ⥤ IsoAlgebra P :=
  IsoAlgebra.mapOfNatIso (P.commShiftIso r)

/-- Upper truncation of fixed pairs, with structure isomorphism
`τ≤m(θ) ∘ c⁻[m,K]` and morphism `τ≤m(u)`. Here `τ≤m = truncLT (m + 1)`;
the comparison is the one normalized by the truncation counit.
Source: BBD 1.3.3(i)--(ii), printed pp. 29--30, and fixed-pair transport in
lem-zl-texact-fixed-pair-heart-cohomology, steps 2--3
(blueprint: def-zl-fixed-pair-truncation-cohomology-functors). -/
abbrev fixedPairTruncLE (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (m : ℤ) :
    IsoAlgebra P ⥤ IsoAlgebra P :=
  IsoAlgebra.mapOfNatIso (P.eTruncLTIso t t (m + 1 : ℤ))

/-- Lower truncation of fixed pairs, with structure isomorphism
`τ≥m(θ) ∘ c⁺[m,K]` and morphism `τ≥m(u)`. The comparison is the canonical
one normalized by the truncation unit, also for unbounded t-structures.
Source: BBD 1.3.3(i)--(ii), printed pp. 29--30, and fixed-pair transport in
lem-zl-texact-fixed-pair-heart-cohomology, steps 2--3
(blueprint: def-zl-fixed-pair-truncation-cohomology-functors). -/
abbrev fixedPairTruncGE (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (m : ℤ) :
    IsoAlgebra P ⥤ IsoAlgebra P :=
  IsoAlgebra.mapOfNatIso (P.eTruncGEIso t t (m : ℤ))

/-- Degree-i cohomology of fixed pairs is the composite of lifted upper truncation,
lifted lower truncation, and lifted shift. Its carrier is `(τ≥i τ≤i K)[i]` and
its carrier map is `(τ≥i τ≤i u)[i]`. All three structure comparisons are the
specified canonical ones, as in `truncationCohomologyComparison`.
Source: BBD 1.3.3--1.3.5, printed pp. 29--31, and fixed-pair transport in
lem-zl-texact-fixed-pair-heart-cohomology, steps 2--3
(blueprint: def-zl-fixed-pair-truncation-cohomology-functors). -/
abbrev fixedPairCohomology (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (i : ℤ) :
    IsoAlgebra P ⥤ IsoAlgebra P :=
  (fixedPairTruncLE t P i ⋙ fixedPairTruncGE t P i) ⋙ fixedPairShift P i

end CategoryTheory.Triangulated.TStructure
