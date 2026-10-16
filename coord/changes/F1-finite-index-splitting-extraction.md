# sumComplEquiv and sumComplEquiv_symm_inl: share the existing finite-index API

## Reason
The landing refusal at head `3f9167606` identifies a duplicate inverse equation in
ContinuousFieldMatrixElimination. Its existing source API in UnitMatrix is independent
of the coefficient field. Directly importing UnitMatrix into the continuous-field path
causes an environment collision between the finite-coefficient and general pro-étale
upper/lower-star APIs. Extract the existing generic definition and proved lemma into
`Sheaf.LinearAlgebra.FiniteIndexSplitting`; UnitMatrix publicly reexports it. No existing
signature, visibility or mathematical value changes. UnitMatrix is unclaimed.

## Old
In `WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix`, under namespace `PadicAlgCl`
and variables `{κ : Type*} [DecidableEq κ]` (unused Fintype instance omitted):

```lean
/-- The splitting `κ ≃ Fin r ⊕ (κ ∖ range ρ)` along an injection `ρ : Fin r → κ`. -/
noncomputable def sumComplEquiv {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) :
    κ ≃ Fin r ⊕ {i // i ∉ Set.range ρ} :=
  (Equiv.sumCompl (· ∈ Set.range ρ)).symm.trans
    (Equiv.sumCongr (Equiv.ofInjective ρ hρ).symm (Equiv.refl _))

omit [Fintype κ] in
@[simp]
lemma sumComplEquiv_symm_inl {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) (a : Fin r) :
    (sumComplEquiv ρ hρ).symm (Sum.inl a) = ρ a := by
  simp [sumComplEquiv]

```

In the proposed, unlanded `ContinuousFieldMatrixElimination`, the same construction and
lemma were repeated in namespace `AlgebraicGeometry.ProEtale`.

## New
The PadicAlgCl definition and lemma above move to
`Sheaf.LinearAlgebra.FiniteIndexSplitting`, with identical elaborated signatures and bodies.
UnitMatrix adds `public import Sheaf.LinearAlgebra.FiniteIndexSplitting` and removes the
original blocks. Its remaining code is unchanged. ContinuousFieldMatrixElimination
publicly imports the same module, removes the duplicate lemma, and replaces its definition by:

```lean
noncomputable abbrev sumComplEquiv {r : ℕ} (ρ : Fin r → κ) (hρ : Function.Injective ρ) :
    κ ≃ Fin r ⊕ {i // i ∉ Set.range ρ} := PadicAlgCl.sumComplEquiv ρ hρ
```

## Users
`tools/downstream.py --uses PadicAlgCl.sumComplEquiv` reports UnitMatrix and
`WeilConjectures.SixFunctors.ProEtale.Adic.Abelian`; the inverse-equation query reports
only UnitMatrix. All 202 import-descendants see the identical names through the public
reexport. No statement becomes weaker, stronger, or different: the moved declarations
keep their elaborated types and definitional values.
The continuous-field modules below belong to this unlanded delivery; their statements
are definitionally unchanged by the alias.

| module | group holding it | effect |
|---|---|---|
| WeilConjectures.SixFunctors.ProEtale.Adic.UnitMatrix | unclaimed | public reexport; original declaration blocks move unchanged |
| WeilConjectures.SixFunctors.ProEtale.Adic.Abelian | unclaimed, not adapted | unchanged uses through UnitMatrix public reexport |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixElimination | F1 (new in delivery) | imports shared API; alias; removes duplicate lemma |
| Sheaf.AlgebraicGeometry.ContinuousFieldMatrixSheafNormalForm | F1 (new in delivery) | no edit; alias keeps statement definitionally identical |

## Status
landed 20261016T005128-L-4190704 2026-10-16 (merge of deliver/F1/Sheaf.AlgebraicGeometry.CondensedFieldLfpLocalTriviality)
