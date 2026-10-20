# AlgebraicGeometry.exists_hasSupportProperOver_baseChange_of_isLimit

## Reason

Retire the duplicate module listed in `coord/retire-items.tsv`, following the human's
2026-10-20 hand-off in `coord/changes/retire-sheaf-twins-20261020.md`.
The adopted upstream theorem already proves the same conclusion, with the unused
Noetherian-ring instance omitted. Keeping two declarations of the same name in
separate modules risks duplicate declarations when their import environments meet.

## Old

Module `Sheaf.AlgebraicGeometry.ProperSupportDescent` declared:

```lean
theorem exists_hasSupportProperOver_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Fi : Xi.Modules) [Fi.IsFinitePresentation]
    (hF : Scheme.Modules.HasSupportProperOver
      (pullback.snd f (c.π.app (op i)))
      ((Scheme.Modules.tensorPullback (pullback.fst f (c.π.app (op i)))).obj Fi)) :
    ∃ (j : I) (hij : i ≤ j),
      Scheme.Modules.HasSupportProperOver
        (pullback.snd f (Spec.map (R.map (homOfLE hij))))
        ((Scheme.Modules.tensorPullback
          (pullback.fst f (Spec.map (R.map (homOfLE hij))))).obj Fi)
```

## New

The Sheaf copy is withdrawn using `deleted.txt`. The node's Lean attachment points to
`WeilConjectures.AlgebraicGeometry.ProperSupportDescent`, which declares:

```lean
theorem exists_hasSupportProperOver_baseChange_of_isLimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (Fi : Xi.Modules) [Fi.IsFinitePresentation]
    (hF : Scheme.Modules.HasSupportProperOver
      (pullback.snd f (c.π.app (op i)))
      ((Scheme.Modules.tensorPullback (pullback.fst f (c.π.app (op i)))).obj Fi)) :
    ∃ (j : I) (hij : i ≤ j),
      Scheme.Modules.HasSupportProperOver
        (pullback.snd f (Spec.map (R.map (homOfLE hij))))
        ((Scheme.Modules.tensorPullback
          (pullback.fst f (Spec.map (R.map (homOfLE hij))))).obj Fi)
```

No adopted-source file or target statement is modified. The original node statement
still follows by direct application; only the redundant Noetherian instance differs.
The source proof follows all four existing node steps, whose dependencies stay attached.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.AlgebraicGeometry.ProperSupportDescent | P6 | Duplicate declaration retired. |
| WeilConjectures.AlgebraicGeometry.ChosenModuleFlatProperStage | unclaimed; unchanged | Already imports the upstream theorem and applies its current API; compiled unchanged. |

`tools/downstream.py Sheaf.AlgebraicGeometry.ProperSupportDescent --uses
AlgebraicGeometry.exists_hasSupportProperOver_baseChange_of_isLimit` reports zero
modules downstream and only the old copy's own declaration as a textual use.
A direct search of `lean/` and `quarantine/` finds no importer of the retired module.
The retirement table's former Sheaf consumer has itself been retired; its DAG node
already points to the upstream consumer above. That node continues to depend on
`lem-pc-proper-support-descent`, now attached upstream. No parent argument or unit
step is removed, and no consumer adaptation is necessary.

## Status

landed 20261020T211813-L-3504025 2026-10-20 (merge of deliver/P6/Sheaf.AlgebraicGeometry.ProperSupportDescent)
