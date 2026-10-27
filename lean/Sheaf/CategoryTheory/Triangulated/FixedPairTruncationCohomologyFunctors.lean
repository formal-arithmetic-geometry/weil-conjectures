module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.TStructure.SpectralObject

/-! # Shift, truncation and cohomology functors on fixed pairs

Source: BBD, Proposition 1.3.3 and §§1.3.4–1.3.5, printed pp. 29–31;
the fixed-pair transport formulas in the blueprint restriction cohomology argument
(blueprint: def-zl-fixed-pair-truncation-cohomology-functors).

These are the existing transport functors specialized to the specified shift and
canonical t-exact truncation comparisons. No triangulation on fixed pairs is used.
-/

@[expose] public section

set_option autoImplicit false

universe u v

namespace CategoryTheory.Triangulated.TStructure

open Limits Endofunctor

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
  [IsTriangulated C]

/-- Shift transport with structure `s` followed by the shifted structure isomorphism.
Source: BBD §1.3, shift convention; the fixed-pair calculation in proof step 1
(blueprint: def-zl-fixed-pair-truncation-cohomology-functors). -/
noncomputable abbrev fixedPairShift (P : C ⥤ C) [P.CommShift ℤ] (r : ℤ) :
    IsoAlgebra P ⥤ IsoAlgebra P :=
  IsoAlgebra.mapOfNatIso (P.commShiftIso r)

/-- Canonical upper truncation transport, with structure `c⁻` followed by `τ≤m(θ)`.
Source: BBD 1.3.3 and the normalized t-exact comparison, proof step 2
(blueprint: def-zl-fixed-pair-truncation-cohomology-functors). -/
noncomputable abbrev fixedPairTruncLE (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (m : ℤ) :
    IsoAlgebra P ⥤ IsoAlgebra P :=
  IsoAlgebra.mapOfNatIso (P.eTruncLTIso t t (m + 1 : ℤ))

/-- Canonical lower truncation transport, with structure `c⁺` followed by `τ≥m(θ)`.
Source: BBD 1.3.3 and the normalized t-exact comparison, proof step 2
(blueprint: def-zl-fixed-pair-truncation-cohomology-functors). -/
noncomputable abbrev fixedPairTruncGE (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (m : ℤ) :
    IsoAlgebra P ⥤ IsoAlgebra P :=
  IsoAlgebra.mapOfNatIso (P.eTruncGEIso t t m)

/-- The composite lifted cohomology functor, with underlying object `(τ≥i τ≤i K)[i]`.
Source: BBD 1.3.3–1.3.6 and the fixed-pair calculation in proof steps 2–3
(blueprint: def-zl-fixed-pair-truncation-cohomology-functors). -/
noncomputable abbrev fixedPairCohomology (t : TStructure C) (P : C ⥤ C)
    [P.CommShift ℤ] [P.IsTriangulated] [P.IsTExact t t] (i : ℤ) :
    IsoAlgebra P ⥤ IsoAlgebra P :=
  fixedPairTruncLE t P i ⋙ fixedPairTruncGE t P i ⋙ fixedPairShift P i

end CategoryTheory.Triangulated.TStructure
