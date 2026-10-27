# finitePerfectAdicEtaleStalk

## Reason

Move the concrete exact derived stalk functor verbatim to
`Sheaf.Paper.FinitePerfectAdicEtaleLevelData`, so the single-level descent record can use
it without importing the theorem that consumes that record. The item publicly imports
this data module. The declaration name, signature and body are identical; no target or
downstream definition changes meaning.

## Old

In `Sheaf.Paper.FinitePerfectAdicEtaleStalkData`:

```lean
def finitePerfectAdicEtaleStalk (Y : Scheme.{t}) (B : Type (t + 1)) [CommRing B]
    (y : Y) : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} B)) ⥤
      DerivedCategory (ModuleCat.{t + 1} B) :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((Y.uliftPointSmallEtale y).sheafFiber (A := ModuleCat.{t + 1} B))
    (Functor.additive_of_preserves_binary_products _) _ _
```

## New

In `Sheaf.Paper.FinitePerfectAdicEtaleLevelData`, reexported by the old module:

```lean
def finitePerfectAdicEtaleStalk (Y : Scheme.{t}) (B : Type (t + 1)) [CommRing B]
    (y : Y) : DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{t + 1} B)) ⥤
      DerivedCategory (ModuleCat.{t + 1} B) :=
  @Functor.mapDerivedCategory _ _ _ _ _ _ _ _
    ((Y.uliftPointSmallEtale y).sheafFiber (A := ModuleCat.{t + 1} B))
    (Functor.additive_of_preserves_binary_products _) _ _
```

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Paper.FinitePerfectAdicEtaleStalkData | F1 | Same declaration via public import; original structure unchanged. |
| Sheaf.Paper.FinitePerfectAdicStalkModels | unmodified consumer | Only direct importer; compiled against this delivery, with no adaptation. |

`tools/downstream.py --uses finitePerfectAdicEtaleStalk` finds only the item itself as a
textual user. No other existing module is modified. The second row records the direct
consumer compatibility check, beyond the textual users.

## Status

landed 20261027T094358-L-219792 2026-10-27 (merge of deliver/F1/Sheaf.Paper.FinitePerfectAdicEtaleStalkData)
