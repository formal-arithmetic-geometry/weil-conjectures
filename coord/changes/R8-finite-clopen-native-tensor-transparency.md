# AlgebraicGeometry.Scheme.ProEt.FiniteClopenTensor.derivedTensorComparison

## Reason

The implicit instance arguments of the inverse derived tensorator triggered unfolding of
large native monoidal constructions during elaboration. Supply the same two prescribed
native monoidal structures and `h.toMonoidal` explicitly, with local transparency settings.
The resulting inverse tensorator, all binders, universes, and its result type are unchanged.
No other public definition body or attribute changes.

## Old

```lean
def derivedTensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (derivedRestriction.{t, u} j R).Braided)
    (K L : DerivedCategory (Modules.{t, u} R)) :
    (derivedRestriction.{t, u} j R).obj (K ⊗ L) ≅
      (derivedRestriction.{t, u} j R).obj K ⊗ (derivedRestriction.{t, u} j R).obj L :=
  letI := h
  (Functor.Monoidal.μIso (derivedRestriction.{t, u} j R) K L).symm
```

## New

```lean
def derivedTensorComparison {X Y : Scheme.{t}} (j : Y ⟶ X) [IsOpenImmersion j]
    (R : Sheaf (topology X) CommRingCat.{max u (t + 1)})
    (h : (derivedRestriction.{t, u} j R).Braided)
    (K L : DerivedCategory (Modules.{t, u} R)) :
    (derivedRestriction.{t, u} j R).obj (K ⊗ L) ≅
      (derivedRestriction.{t, u} j R).obj K ⊗ (derivedRestriction.{t, u} j R).obj L := by
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      exact (@Functor.Monoidal.μIso _ _ (derivedMonoidal.{t, u} R) _ _
        (derivedMonoidal.{t, u} ((rings.{t, u} j).obj R))
        (derivedRestriction.{t, u} j R) h.toMonoidal K L).symm
```

## Users

The declaration-use scan finds only the item module itself. The direct importers below
were also checked against the delivered module and need no source edits.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus | R8 | Uses the same inverse native tensorator; unchanged theorem statements compile. |
| Sheaf.Paper.FiniteClopenDerivedDecomposition | unclaimed | Original source compiles; no adaptation. |
| Sheaf.Paper.SfClopenDerivedCompatibility | unclaimed | Original source compiles; no adaptation. |

No target statement or interpretation changes: the construction is the original
`Functor.Monoidal.μIso` with its existing arguments made explicit. The original restriction,
localization, and native derived tensor data remain verbatim.

## Status

landed 20261022T114242-L-595400 2026-10-22 (merge of deliver/R8/Sheaf.AlgebraicGeometry.ProEtaleFiniteClopenTensorCalculus)
