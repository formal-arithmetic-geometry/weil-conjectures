/-
Copyright (c) 2026 The SHEAF contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SHEAF group F1
-/
module

public import Sheaf.AlgebraicGeometry.DerivedCategory
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs

/-!
# An upper cohomological bound for an unbounded derived functor

Source: Stacks Project, Derived Categories of Schemes, Tag 08D4, part (3), upper-bound
clause (blueprint: lem-pc-unbounded-derived-functor-cohomological-bound).
-/

@[expose] public section

universe u w w'

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- An additive functor commuting with countable products and with `R^p F = 0` on
quasi-coherent modules for `p ≥ N` sends quasi-coherent derived objects supported in
degrees at most `b` to objects supported in degrees at most `b + N - 1`.

Source: Stacks Project, Tag 08D4, part (3), upper-bound clause
(blueprint: lem-pc-unbounded-derived-functor-cohomological-bound).

Proof:
1. Set `E_n = τ_{≥ -n} E` for natural numbers `n`. Reconstruct `E` as its derived
inverse limit and commute `RF` with that limit, using
`lem-pc-qcoh-truncation-derived-limit` (Tags 08D3 and 08U1).
2. Apply `lem-pc-derived-limit-milnor-sequence` to obtain the short exact sequence
from the first derived limit of `H^{i-1}(RF(E_n))` to `H^i(RF(E))` to the limit of
`H^i(RF(E_n))` (Tag 07KY).
3. The truncation triangle has endpoints `H^{-n}(E)[n]` and `H^{-n}(E)[n+1]`.
Their degree `i` images vanish for `n ≥ N-i`, so
`lem-pc-derived-functor-truncation-stabilization` gives isomorphisms on degree `i`
cohomology between successive truncations.
4. These towers are eventually constant and hence Mittag--Leffler. Their first
derived limits vanish, and ordinary limits identify with the stable terms
(Tag 07KW). Thus degree `i` cohomology of `RF(E)` agrees with a sufficiently late
truncation term; stabilization extends this identification to `E_{N-i-1}`.
5. For `i ≥ b+N`, stabilization continues down to `E_{-b-1} = τ_{≥ b+1} E`.
This truncation is zero by `def-sbc-standard-tstructure-derived-category` and
the assumed upper support bound. Since `RF(0) = 0`, the desired cohomology vanishes.
-/
theorem isZero_homology_rightDerivedFunctor_of_cohomological_bound
    (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w'} AddCommGrpCat.{u}]
    [Abelian.HasKInjectiveResolutions
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasInjectiveResolutions (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (F : SheafOfModules.{u} (moduleRings X.toRingedSpace) ⥤ AddCommGrpCat.{u})
    [F.Additive] [PreservesLimitsOfShape (Discrete ℕ) F]
    (N : ℕ)
    (hN : ∀ (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      M.IsQuasicoherent → ∀ p : ℕ, N ≤ p → IsZero ((F.rightDerived p).obj M))
    (b : ℤ) (E : schemeDerivedCategory X) (hE : schemeDerivedQCohProperty X E)
    (hb : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj E)) :
    ∀ i : ℤ, b + (N : ℤ) - 1 < i →
      IsZero ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        (F.rightDerivedFunctor.obj E)) := by
  sorry

end AlgebraicGeometry
