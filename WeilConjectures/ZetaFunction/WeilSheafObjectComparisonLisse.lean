/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilSheaf.WeilDescent
public import WeilConjectures.ZetaFunction.WeilObjectComparisonPullback
public import WeilConjectures.ZetaFunction.WeilObjectComparisonTwist
public import WeilConjectures.ZetaFunction.WeilSheafObjectComparisonInduction

/-!
# Irreducible lisse Weil sheaves have the traces of Weil objects

The generic case of the Noetherian induction of
`WeilConjectures.ZetaFunction.WeilSheafObjectComparisonInduction`: on a smooth irreducible
separated `k₀`-scheme `V₀` of finite type, every irreducible lisse Weil sheaf `G` has, through
the canonical identification `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`, the traces of a Weil object. Indeed
`G ≅ p^* H ⊗ 𝓑_b` for a lisse sheaf `H` on `V₀`
(`AlgebraicGeometry.WeilSheaf.IsIrreducibleLisse.exists_iso_constantTwist_geometricFiberPullback`),
`p^* H` has the traces of the Weil object `H`
(`AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_geometricFiberPullback`), and
constant twists preserve the comparison
(`AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_constantTwist`).

## Main results

- `AlgebraicGeometry.WeilSheaf.irreducibleLisseComparisonHolds`.
- `AlgebraicGeometry.WeilSheaf.lisseComparisonHolds`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

open ProEtale.CondensedRing

/-- **Irreducible lisse Weil sheaves have the traces of Weil objects**, through the canonical
identification `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`. -/
theorem irreducibleLisseComparisonHolds :
    IrreducibleLisseComparisonHolds (k₀ := k₀) (l := l)
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom := by
  intro V _ _ _ _ _ _ _ G hG
  obtain ⟨H, hH, b, ⟨e⟩⟩ := hG.exists_iso_constantTwist_geometricFiberPullback
  exact .of_iso (toComplex.mapIso e.symm)
    (hasWeilObjectComparison_toComplex_constantTwist b
      (hasWeilObjectComparison_toComplex_geometricFiberPullback hH))

/-- **Lisse Weil sheaves have the traces of Weil objects**, through the canonical
identification `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`. -/
theorem lisseComparisonHolds :
    LisseComparisonHolds (k₀ := k₀) (l := l)
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom :=
  lisseComparisonHolds_of_irreducibleLisseComparisonHolds irreducibleLisseComparisonHolds

end AlgebraicGeometry.WeilSheaf
