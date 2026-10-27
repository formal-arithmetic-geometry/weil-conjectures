# FiniteIndexSplitting.sumComplEquiv

## Reason

Importing the completeness dependencies together with the proper-image dependencies fails:
`import Sheaf.LinearAlgebra.FiniteIndexSplitting failed, environment already contains
PadicAlgCl.sumComplEquiv_symm_inl from WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix`.
The extracted Sheaf module reused two names still defined in the adopted source. Give the
extracted declarations their own namespace. The source library is unchanged. The definitions,
lemma statements, proofs and attributes are otherwise identical, including the empty-type and
rank-zero cases. No target's mathematical meaning changes.

## Old

```lean
namespace PadicAlgCl

variable {κ : Type*} [DecidableEq κ]

noncomputable def sumComplEquiv {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) :
    κ ≃ Fin r ⊕ {i // i ∉ Set.range ρ} :=
  (Equiv.sumCompl (· ∈ Set.range ρ)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective ρ hρ).symm (Equiv.refl _))

@[simp]
lemma sumComplEquiv_symm_inl {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) (a : Fin r) :
    (sumComplEquiv ρ hρ).symm (Sum.inl a) = ρ a := by
  simp [sumComplEquiv]

end PadicAlgCl
```

## New

```lean
namespace FiniteIndexSplitting

variable {κ : Type*} [DecidableEq κ]

noncomputable def sumComplEquiv {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) :
    κ ≃ Fin r ⊕ {i // i ∉ Set.range ρ} :=
  (Equiv.sumCompl (· ∈ Set.range ρ)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective ρ hρ).symm (Equiv.refl _))

@[simp]
lemma sumComplEquiv_symm_inl {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) (a : Fin r) :
    (sumComplEquiv ρ hρ).symm (Sum.inl a) = ρ a := by
  simp [sumComplEquiv]

end FiniteIndexSplitting
```

The one direct consumer's public `AlgebraicGeometry.ProEtale.sumComplEquiv` abbreviation now refers to
`FiniteIndexSplitting.sumComplEquiv`; its signature and expanded value are unchanged.
The original `PadicAlgCl` API remains verbatim in `WeilConjectures/.../Adic/UnitMatrix.lean`.

## Users

The declaration search of `tools/downstream.py --uses` lists the following modules.
Its short-name matches include independent local declarations; those need no changes.
Neither modified module has a claim record on this checkout.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.LinearAlgebra.FiniteIndexSplitting | unclaimed | namespace repair |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixElimination | unclaimed | one qualified reference |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | unclaimed | uses unchanged public abbreviation; no edit |
| Sheaf.Paper.CondensedQbarLfpMatrixRefinement | unclaimed | independent private definitions; no edit |

The 1887 transitive importers retain the same expanded equivalence and simp equation.
No declaration under `WeilConjectures` is changed or removed.

## Status

landed 20261024T214903-L-727387 2026-10-24 (merge of deliver/F2/Sheaf.Paper.IntegralProperBaseChange)
