# AlgebraicGeometry.exists_flat_module_on_later_stage

## Reason

Retire the duplicate `Sheaf.AlgebraicGeometry.FlatModuleOnLaterStage` in favor of
`WeilConjectures.AlgebraicGeometry.FlatModuleOnLaterStage`, as listed in
`coord/retire-items.tsv`. The row says DIFFERENT because the source twin lacks
`flatOver_of_iso`; that helper is private. The public theorem signatures are
byte-for-byte identical. The source twin uses the proved public
`Scheme.Modules.IsFlatOver.of_iso` API instead. Its complete axiom closure was checked
through lcompile: only `propext`, `Classical.choice`, and `Quot.sound` occur.

The sole direct importer is migrated in the same packet. The node is retained and
attached to the adopted source declaration. Its parent's existing dependency on this
node is retained, and the parent's proof step names the replacement module explicitly.
The unit's Noetherian approximation route and every theorem statement stay the same.
No adopted source file is edited or removed. No target definition changes.

## Old

Module `Sheaf.AlgebraicGeometry.FlatModuleOnLaterStage`:

```lean
theorem exists_flat_module_on_later_stage
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Zi : Scheme.{u}} (fi : Zi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation fi] [QuasiCompact fi] [QuasiSeparated fi]
    (M : (pullback fi (c.π.app (Opposite.op i))).Modules) [M.IsFinitePresentation]
    (hM : M.IsFlatOver (pullback.snd fi (c.π.app (Opposite.op i)))) :
    ∃ (j : I) (hij : i ≤ j)
      (Mj : (pullback fi (Spec.map (R.map (homOfLE hij)))).Modules),
      Mj.IsFinitePresentation ∧
      Mj.IsFlatOver (pullback.snd fi (Spec.map (R.map (homOfLE hij)))) ∧
      Nonempty ((Scheme.Modules.moduleBaseChange fi
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (Opposite.op i)))
        (Over.homMk (c.π.app (Opposite.op j)) (c.w (homOfLE hij).op))).obj Mj ≅ M)
```

In `Sheaf.AlgebraicGeometry.ProperFlatSingleNoetherianDescent`:

```lean
import Sheaf.AlgebraicGeometry.FlatModuleOnLaterStage
```

## New

The same declaration in `WeilConjectures.AlgebraicGeometry.FlatModuleOnLaterStage`:

```lean
theorem exists_flat_module_on_later_stage
    {I : Type u} [PartialOrder I] [IsDirectedOrder I]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Zi : Scheme.{u}} (fi : Zi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation fi] [QuasiCompact fi] [QuasiSeparated fi]
    (M : (pullback fi (c.π.app (Opposite.op i))).Modules) [M.IsFinitePresentation]
    (hM : M.IsFlatOver (pullback.snd fi (c.π.app (Opposite.op i)))) :
    ∃ (j : I) (hij : i ≤ j)
      (Mj : (pullback fi (Spec.map (R.map (homOfLE hij)))).Modules),
      Mj.IsFinitePresentation ∧
      Mj.IsFlatOver (pullback.snd fi (Spec.map (R.map (homOfLE hij)))) ∧
      Nonempty ((Scheme.Modules.moduleBaseChange fi
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (c.π.app (Opposite.op i)))
        (Over.homMk (c.π.app (Opposite.op j)) (c.w (homOfLE hij).op))).obj Mj ≅ M)
```

In `Sheaf.AlgebraicGeometry.ProperFlatSingleNoetherianDescent`:

```lean
import WeilConjectures.AlgebraicGeometry.FlatModuleOnLaterStage
```

The old Sheaf module is withdrawn using `deleted.txt`; the delivery tool creates
its empty module. The original theorem remains available from the source module.
The parent has exactly one changed import line; all its proofs, public imports,
signatures, visibility and definitions remain verbatim.

## Users

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.FlatModuleOnLaterStage | C7 (assigned item) | Withdraw duplicate; node points to the identical source theorem. |
| Sheaf.AlgebraicGeometry.ProperFlatSingleNoetherianDescent | unclaimed in current shared claim records | Replace sole private import; identical theorem used at the same proof step. |
| Sheaf.AlgebraicGeometry.DescentFirstProperFlatCechModel | unchanged; not adapted | Transitive consumer reported by downstream.py; public interface of its imported parent is unchanged. |

These are all modules listed by `tools/downstream.py
Sheaf.AlgebraicGeometry.FlatModuleOnLaterStage --uses
AlgebraicGeometry.exists_flat_module_on_later_stage`. A whole-library import search
finds just the one direct importer. DAG and unit searches find only the item's node
and its one parent, both included in this packet; no quarantined parent is listed for
this item in `coord/rework.tsv`.

## Status

landed 20261021T002129-L-1489967 2026-10-21 (merge of deliver/C7/Sheaf.AlgebraicGeometry.FlatModuleOnLaterStage)
