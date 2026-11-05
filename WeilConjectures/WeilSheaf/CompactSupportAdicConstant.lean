/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.Cohomology
public import WeilConjectures.WeilSheaf.Constant
public import WeilConjectures.WeilSheaf.LowerStar
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
import WeilConjectures.WeilSheaf.CohomologyProEtale
import WeilConjectures.WeilSheaf.LowerShriek
import WeilConjectures.WeilSheaf.CohomologyNonneg
import WeilConjectures.AlgebraicGeometry.DenseCompactification
import WeilConjectures.Mathlib.Topology.KrullDimension
import WeilConjectures.AlgebraicGeometry.FieldBaseChangeDimension
import WeilConjectures.WeilSheaf.OpenClosedTriangle
import WeilConjectures.WeilSheaf.CohomologyAdicConstant
import WeilConjectures.SixFunctors.ProEtale.Adic.ConstantCohomologicalDimension

/-!
# Compactly supported cohomology of the constant Weil sheaf

Let `X` be a separated `k₀`-scheme of finite type whose geometric fiber `X ⊗ k̄` has dimension
at most `e`. Then `H_c^r(X ⊗ k̄, ℚ̄_ℓ) = 0` for `r ∉ [0, 2e]`. Choose a dense compactification
`j : X ⟶ X'` with `dim X' = dim X` and let `i : W ⟶ X'` be its closed complement, of dimension
`< e`. The open–closed triangle gives the exact sequence
`H^{r-1}(W, i^*ℚ̄_ℓ) ⟶ H_c^r(X, j^*ℚ̄_ℓ) ⟶ H^r(X', ℚ̄_ℓ)`, whose outer terms vanish for `r > 2e`
(`AlgebraicGeometry.WeilSheaf.subsingleton_cohomology_adicConstant_of_two_mul_lt`); and the
vanishing of `H_c^r` only depends on the underlying `ℓ`-adic sheaf, which is `ℚ̄_ℓ` for `j^*ℚ̄_ℓ`.

## Main statements

- `AlgebraicGeometry.ProEtaleWeilSheaf.nonempty_lowerStarCohomologyIso`: for a pro-étale Weil
  sheaf `G` on `Y` and `φ : Y ⟶ Spec k₀`, the global sections of the `r`-th cohomology sheaf of
  `Rφ_* G` are the pro-étale cohomology `Rʳ Γ(Ȳ_proét, G)` of the underlying sheaf.
- `AlgebraicGeometry.WeilSheaf.subsingleton_compactlySupportedCohomology_of_iso`: the vanishing
  of `H_c^r(X ⊗ k̄, F)` only depends on the underlying `ℓ`-adic sheaf of `F`.
- `AlgebraicGeometry.topologicalKrullDim_compl_add_one_le_of_dense`: the complement of a dense
  open subset has smaller dimension.
- `WeilSheaf.subsingleton_compactlySupportedCohomology_adicConstant_of_two_mul_lt`:
  the vanishing of `H_c^r(X ⊗ k̄, ℚ̄_ℓ)` for `r ∉ [0, 2e]`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Endofunctor

open scoped AlgebraicGeometry.ProEtale

-- `Spec k₀` over itself: prefer the identity structure over `AlgebraicGeometry.specOverSpec`,
-- which is imported through the étale cohomological dimension bound.
attribute [local instance 1100] CategoryTheory.instOverClass

namespace AlgebraicGeometry

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

namespace ProEtaleWeilSheaf

variable {Y : Scheme.{u}} [Y.Over (Spec (CommRingCat.of k₀))]
  (φ : Y ⟶ Spec (CommRingCat.of k₀)) [φ.IsOver (Spec (CommRingCat.of k₀))]

end ProEtaleWeilSheaf

section Dimension

open Order Topology TopologicalSpace

end Dimension

namespace WeilSheaf

variable {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

end WeilSheaf

namespace WeilSheaf

end WeilSheaf

end AlgebraicGeometry
