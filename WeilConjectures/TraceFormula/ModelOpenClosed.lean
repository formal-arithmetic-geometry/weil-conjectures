/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.TraceFormula.FibreModel

/-!

# Open–closed decompositions of a model

Let `Φ` be the model Frobenius of a model `X₀` of `X = X₀ ×_{k₀} k` over a finite field `k₀`.
For an affine open `U₀ ⊆ X₀` with reduced closed complement `Z₀`, the base changes `U` and `Z`
of `U₀` and `Z₀` are an open subscheme of `X` and its closed complement, both stable under `Φ`,
with the model Frobenii of `U₀` and `Z₀` (blueprint `thm-trf-coefficient-morphism-trace-formula`,
Step 5). The complement `Z₀` is covered by one affine open fewer than `X₀`.

## Main results

- `ProEtale.CondensedRing.IsModelFrobenius.exists_finset_isAffineOpen`: the model of a
  quasi-compact `X` is covered by finitely many affine opens.
- `ProEtale.CondensedRing.IsModelFrobenius.isProper_of_card_eq_zero`: if the model is covered by
  no affine open, `X` is empty, hence proper.
- `ProEtale.CondensedRing.IsModelFrobenius.exists_isCompl`: the open–closed decomposition along
  an affine open of the model.

-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.ProEtale.CondensedRing

open Scheme

variable {k : Type u} [Field k] {X : Over (Spec (.of k))} [LocallyOfFiniteType X.hom]
  [QuasiCompact X.hom] [IsSeparated X.hom] {Φ : X ⟶ X}
  {k₀ : Type u} [Field k₀] [Finite k₀] [Algebra k₀ k] {X₀ : Scheme.{u}}
  {f₀ : X₀ ⟶ Spec (.of k₀)} {p : X.left ⟶ X₀}

/-- The model `X₀` of a quasi-compact `X` is covered by finitely many affine opens: it is the
image of `X` under the surjective projection `p`. -/
theorem IsModelFrobenius.exists_finset_isAffineOpen (hΦ : IsModelFrobenius Φ f₀ p) :
    ∃ s : Finset X₀.Opens, (∀ U ∈ s, IsAffineOpen U) ∧ ⨆ U ∈ s, U = ⊤ :=
  sorry

/-- If the model `X₀` is covered by no affine open, it is empty, hence so is `X`, and `X` is
proper over `k`. -/
theorem IsModelFrobenius.isProper_of_card_eq_zero (hΦ : IsModelFrobenius Φ f₀ p)
    {s : Finset X₀.Opens} (hs : s.card = 0) (hcov : ⨆ U ∈ s, U = ⊤) : IsProper X.hom :=
  sorry

/-- **Open–closed decomposition along an affine open of the model** (blueprint
`thm-trf-coefficient-morphism-trace-formula`, Step 5): if the model `X₀` is covered by the
affine opens of a finite set `s` of `n + 1` elements, there are an open immersion `j : U ⟶ X` and
a closed immersion `i : Z ⟶ X` with complementary images, endomorphisms `Φ_U`, `Φ_Z` with
`Φ_U ≫ j = j ≫ Φ` and `Φ_Z ≫ i = i ≫ Φ` which are model Frobenii over `k₀`, the model of `U`
being affine and the model of `Z` being covered by `n` affine opens. -/
theorem IsModelFrobenius.exists_isCompl [IsAlgClosed k] [LocallyOfFiniteType f₀]
    (hΦ : IsModelFrobenius Φ f₀ p) {n : ℕ} {s : Finset X₀.Opens} (hs : s.card = n + 1)
    (hsa : ∀ U ∈ s, IsAffineOpen U) (hcov : ⨆ U ∈ s, U = ⊤) :
    ∃ (U : Over (Spec (.of k))) (_ : LocallyOfFiniteType U.hom) (_ : QuasiCompact U.hom)
      (_ : IsSeparated U.hom) (Z : Over (Spec (.of k))) (_ : LocallyOfFiniteType Z.hom)
      (_ : QuasiCompact Z.hom) (_ : IsSeparated Z.hom) (j : U ⟶ X) (i : Z ⟶ X)
      (_ : IsOpenImmersion j.left) (_ : IsClosedImmersion i.left) (ΦU : U ⟶ U) (ΦZ : Z ⟶ Z)
      (U₀ : Scheme.{u}) (fU₀ : U₀ ⟶ Spec (.of k₀)) (pU : U.left ⟶ U₀)
      (Z₀ : Scheme.{u}) (fZ₀ : Z₀ ⟶ Spec (.of k₀)) (pZ : Z.left ⟶ Z₀)
      (t : Finset Z₀.Opens),
      ΦU ≫ j = j ≫ Φ ∧ ΦZ ≫ i = i ≫ Φ ∧
        IsCompl (Set.range j.left.base) (Set.range i.left.base) ∧
        IsAffine U₀ ∧ LocallyOfFiniteType fU₀ ∧ IsModelFrobenius ΦU fU₀ pU ∧
        LocallyOfFiniteType fZ₀ ∧ IsModelFrobenius ΦZ fZ₀ pZ ∧
        t.card = n ∧ (∀ V ∈ t, IsAffineOpen V) ∧ ⨆ V ∈ t, V = ⊤ :=
  sorry

end AlgebraicGeometry.ProEtale.CondensedRing
