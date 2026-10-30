/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.WeilObject.Sheaf.EndTensorUnit
public import WeilConjectures.WeilSheaf.GeometricFiberPullback
public import WeilConjectures.ZetaFunction.WeilSheafObjectComparisonInduction

/-!
# The comparison of lisse Weil sheaves with Weil objects

The Noetherian induction of
`WeilConjectures.ZetaFunction.WeilSheafObjectComparisonInduction` reduces the comparison of Weil
sheaves with Weil objects (`AlgebraicGeometry.WeilComplex.HasWeilObjectComparison`) to irreducible
lisse Weil sheaves on smooth irreducible affine `k₀`-schemes
(`AlgebraicGeometry.WeilSheaf.IrreducibleLisseComparisonHolds`). This file splits that case in
two:

* **Descent** (`AlgebraicGeometry.WeilSheaf.exists_iso_constantTwist_geometricFiberPullback`):
  an irreducible lisse Weil sheaf `G` on a smooth irreducible `V₀` is a constant twist
  `p^* H ⊗ 𝓑_b` of the pullback of a lisse `ℓ`-adic sheaf `H` on `V₀` itself, along the
  projection `p : V₀ ⊗ k̄ ⟶ V₀` (Deligne, Weil II, 1.3.14, and the dictionary between lisse
  sheaves on `V₀` and continuous representations of `π₁(V₀)`).
* **Pulled-back sheaves**
  (`AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_constantTwist_geometricFiberPullback`):
  the Weil sheaf `p^* H ⊗ 𝓑_b` has the traces of the Weil object `(H, b)` of
  `Dᵇc(V₀)⟦ℚ̲̄_ℓ⟧` for the identity, `H` in degree `0` with the structure automorphism `b`:
  the stalks of `p^* H` are those of `H`, and its compactly supported cohomology is that of `H`,
  compatibly with the Frobenius.

## Main results

- `AlgebraicGeometry.WeilSheaf.irreducibleLisseComparisonHolds`: the generic case of the
  Noetherian induction.
- `AlgebraicGeometry.WeilSheaf.hasWeilObjectComparison_toComplex_of_irreducibleLisse`: every
  Weil sheaf has the traces of a Weil object, through the canonical identification
  `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.WeilSheaf

open ProEtale ProEtale.CondensedRing

variable {k₀ : Type u} [Field k₀] [Finite k₀] {l : ℕ} [Fact l.Prime] [Fact (ringChar k₀ ≠ l)]

/-- **Descent of irreducible lisse Weil sheaves** (Deligne, Weil II, 1.3.14): an irreducible
lisse Weil sheaf `G` on a smooth irreducible affine separated `k₀`-scheme `V₀` of finite type is
the constant twist `p^* H ⊗ 𝓑_b` of the pullback, with its canonical Weil structure, of a lisse
`ℓ`-adic sheaf `H` on `V₀` along the projection `p : V₀ ⊗ k̄ ⟶ V₀`. -/
theorem exists_iso_constantTwist_geometricFiberPullback (V : Scheme.{u})
    [V.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (V ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (V ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (V ↘ Spec (CommRingCat.of k₀))] [Smooth (V ↘ Spec (CommRingCat.of k₀))]
    [IrreducibleSpace V] [IsAffine V] (G : WeilSheaf k₀ l V) (hG : G.IsIrreducibleLisse) :
    ∃ (H : AdicSheaf l V) (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ),
      Nonempty (G ≅ (WeilSheaf.geometricFiberPullback (k₀ := k₀) hH).constantTwist b) :=
  sorry

/-- **Pulled-back lisse sheaves have the traces of Weil objects**: for a lisse `ℓ`-adic sheaf
`H` on `X₀` and a unit `b ∈ ℚ̄_ℓ`, the constant twist `p^* H ⊗ 𝓑_b` of its pullback to
`X₀ ⊗ k̄` has, through the canonical identification `End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`, the traces
of the Weil object `(H, b)` of `Dᵇc(X₀)⟦ℚ̲̄_ℓ⟧` for the identity. -/
theorem hasWeilObjectComparison_constantTwist_geometricFiberPullback
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))]
    {H : AdicSheaf l X} (hH : IsAdicLisseSheaf H) (b : (PadicAlgCl l)ˣ) :
    WeilComplex.HasWeilObjectComparison
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom
      (toComplex.obj ((WeilSheaf.geometricFiberPullback (k₀ := k₀) hH).constantTwist b)) :=
  sorry

/-- The generic case of the Noetherian induction: irreducible lisse Weil sheaves on smooth
irreducible affine `k₀`-schemes have the traces of Weil objects. -/
theorem irreducibleLisseComparisonHolds :
    IrreducibleLisseComparisonHolds (k₀ := k₀) (l := l)
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom := by
  intro V _ _ _ _ _ _ _ G hG
  obtain ⟨H, hH, b, ⟨e⟩⟩ := exists_iso_constantTwist_geometricFiberPullback V G hG
  exact (hasWeilObjectComparison_constantTwist_geometricFiberPullback hH b).of_iso
    (toComplex.mapIso e.symm)

/-- **Weil sheaves have the traces of Weil objects**, through the canonical identification
`End (𝟙_ Mod_{Spec k̄}) ≅ ℚ̄_ℓ`, by Noetherian induction from
`AlgebraicGeometry.WeilSheaf.irreducibleLisseComparisonHolds`. -/
theorem hasWeilObjectComparison_toComplex_of_irreducibleLisse
    {X : Scheme.{u}} [X.Over (Spec (CommRingCat.of k₀))]
    [IsSeparated (X ↘ Spec (CommRingCat.of k₀))]
    [LocallyOfFiniteType (X ↘ Spec (CommRingCat.of k₀))]
    [QuasiCompact (X ↘ Spec (CommRingCat.of k₀))] (G : WeilSheaf k₀ l X) :
    WeilComplex.HasWeilObjectComparison
      (endTensorUnitRingEquiv l (AlgebraicClosure k₀)).toAddMonoidHom (toComplex.obj G) :=
  hasWeilObjectComparison_toComplex_of_lisseComparisonHolds
    (lisseComparisonHolds_of_irreducibleLisseComparisonHolds irreducibleLisseComparisonHolds) G

end AlgebraicGeometry.WeilSheaf
