# CategoryTheory.ConstantCompletion.ordinaryLimit

## Reason

The complex constructions repeatedly inferred that the ordinary limit preserves zero
maps through the general right-adjoint machinery. Give the same limit functor its
canonical additive proof, and name the complex functor over an abstract coefficient
category before specializing it. The unit proof now specializes that same named functor,
so kernel checking does not normalize the two complex-functor constructions separately.
The helper unfolds to the original construction, and zero-map preservation is a
proposition. Proof irrelevance therefore identifies the instance arguments. A Lean
`rfl` check verifies definitional equality of the complete old and new functors.
No object, map, theorem statement or target meaning changes.

## Old

```lean
abbrev ordinaryLimit (O : Sheaf J CommRingCat.{u}) :
    CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ ⥤ Cx O :=
  (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O).mapHomologicalComplex (ComplexShape.up ℤ)
```

## New

```lean
def complexLimitFunctor (M : Type*) [Category M] [Preadditive M]
    [HasLimitsOfShape ℕᵒᵖ M] [(lim : (ℕᵒᵖ ⥤ M) ⥤ M).PreservesZeroMorphisms] :
    CochainComplex (ℕᵒᵖ ⥤ M) ℤ ⥤ CochainComplex M ℤ :=
  (lim : (ℕᵒᵖ ⥤ M) ⥤ M).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The ordinary termwise limit of strict tower complexes. Source: Stacks 0940
(blueprint: lem-weil-pbc-constant-completion-equivalence). -/
abbrev ordinaryLimit (O : Sheaf J CommRingCat.{u}) :
    CochainComplex (ℕᵒᵖ ⥤ Mod O) ℤ ⥤ Cx O :=
  letI : (lim : (ℕᵒᵖ ⥤ Mod O) ⥤ Mod O).Additive :=
    Functor.additive_of_preserves_binary_products _
  complexLimitFunctor (Mod O)
```

## Users

A Lean normalization check proved equality of the old and new functors by `rfl` and
compiled in 8.5 seconds. Thus every existing use is definitionally unchanged.
A source search finds uses of `ConstantCompletion.ordinaryLimit` only in the assigned
module. The declarations named `ordinaryLimit` in `IntegralDirectImageTower` and
`CompletedCoefficientPushforwardComparison` are unrelated homonyms in other namespaces.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.ConstantCompletionEquivalence | V6 | Uses exactly the same complex limit functor, with a shorter instance argument. |
| Sheaf.Paper.CompletedCoefficientPushforwardComparison | unclaimed | The consumer scan finds the unrelated `DiagramComparisonData.ordinaryLimit` field in namespace `WeilConjectures.CompletedCoefficientPushforward`; it does not use `CategoryTheory.ConstantCompletion.ordinaryLimit`. No adaptation is needed. |
| Sheaf.Paper.IntegralDirectImageTower | M2 | The consumer scan finds its own `AlgebraicGeometry.ProEtale.IntegralDirectImageTower.ordinaryLimit`; it does not use `CategoryTheory.ConstantCompletion.ordinaryLimit`. No adaptation is needed. |

No consumer requires adaptation.

## Status

landed 20261020T230839-L-620015 2026-10-20 (merge of deliver/V6/Sheaf.Paper.ConstantCompletionEquivalence)
