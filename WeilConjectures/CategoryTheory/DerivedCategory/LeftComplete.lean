/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimit
public import WeilConjectures.Algebra.Homology.DerivedCategory.TowerLimitRange
public import WeilConjectures.Algebra.Homology.HomotopyCategory.Products
public import WeilConjectures.CategoryTheory.Triangulated.HomotopyLimit.Basic
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# Left completeness of derived categories with exact countable products

Let `C` be an abelian category with K-injective resolutions in which countable products exist
and are exact (for instance sheaves of modules on a replete site, such as the pro-étale site).
Then the derived category `D(C)` is *left complete*: every object `K` is the homotopy limit of
the tower `⋯ ⟶ τ_{≥ -1} K ⟶ τ_{≥ 0} K` of its truncations
(`DerivedCategory.isHomotopyLimit_truncGECone`, Bhatt–Scholze, *The pro-étale topology for
schemes*, Proposition 3.3.3, blueprint `sk-prop-pe-left-complete`).

Indeed, let `W` be the homotopy limit, the fibre of `1 - t` on `∏ₙ τ_{≥ -n} K`. Products being
exact, `Hⁱ(∏ₙ τ_{≥ -n} K) = ∏ₙ Hⁱ(τ_{≥ -n} K)`, and the tower `Hⁱ(τ_{≥ -n} K)` vanishes for
`n < -i` and is constant equal to `Hⁱ(K)` from there on. For such a tower `1 - t` is a split
epimorphism (`CategoryTheory.Limits.epi_one_sub_of_isZero_of_isIso`) and its kernel is the
limit `Hⁱ(K)` (`CategoryTheory.Limits.isLimitOfIsZeroOfIsIso`). The homology sequence of the
Milnor triangle then shows that `K ⟶ W` induces isomorphisms on all `Hⁱ`.

As a consequence, a triangulated functor `G` preserving countable products, with values in a
derived category with exact countable products, sends an object `K` into degrees `≤ b + 1` as
soon as it sends all truncations `τ_{≥ -n} K` into degrees `≤ b`
(`DerivedCategory.isLE_obj_of_forall_isLE_obj_truncGE`).
-/

@[expose] public section

open CategoryTheory Category Limits Opposite Pretriangulated

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Preadditive C]

end CategoryTheory.Limits

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

open TStructure (t)

variable [Abelian.HasKInjectiveResolutions C] [HasLimitsOfShape (Discrete ℕ) C]
  [HasExactLimitsOfShape (Discrete ℕ) C]

section Amplitude

variable {D : Type*} [Category* D] [Abelian D] [HasDerivedCategory D]
  [Abelian.HasKInjectiveResolutions D] [HasLimitsOfShape (Discrete ℕ) D]
  [HasExactLimitsOfShape (Discrete ℕ) D]

end Amplitude

end DerivedCategory
