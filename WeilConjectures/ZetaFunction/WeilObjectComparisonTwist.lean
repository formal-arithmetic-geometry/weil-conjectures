/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import WeilConjectures.WeilSheaf.Tensor
public import WeilConjectures.ZetaFunction.WeilObjectComparisonDevissage

/-!
# Constant twists and the comparison with Weil objects

The comparison `AlgebraicGeometry.WeilComplex.HasWeilObjectComparison` of a Weil sheaf with the
Weil objects of the trace formula chapter is preserved by constant twists: if `K'` is a Weil
object for `G`, then `K'` with its Weil structure multiplied by `b` is a Weil object for the
constant twist `G ⊗ 𝓑_b` (`AlgebraicGeometry.WeilSheaf.constantTwist`). In degree `n` all
local and global traces are multiplied by `bⁿ` on both sides.

## Main results

- `AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_constantTwist`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]
  {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
  [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
  [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
  [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]

open ProEtale.CondensedRing in
/-- **Constant twists preserve the comparison with Weil objects**: if a Weil sheaf `G` has the
traces of a Weil object `K'` through the canonical identification
`End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`, then its constant twist `G ⊗ 𝓑_b` has the traces of `K'` with
its Weil structure multiplied by `b`: in degree `n` both the trace function and the compactly
supported traces are multiplied by `bⁿ`. -/
theorem hasWeilObjectComparison_toComplex_constantTwist {G : WeilSheaf k₀ l X}
    (b : (PadicAlgCl l)ˣ)
    (hG : WeilComplex.HasWeilObjectComparison
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom (toComplex.obj G)) :
    WeilComplex.HasWeilObjectComparison
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom
      (toComplex.obj (G.constantTwist b)) :=
  sorry

end AlgebraicGeometry.WeilSheaf
