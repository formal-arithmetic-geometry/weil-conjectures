# SheafOfModules.exists_stalk_directSum_linearEquiv

## Reason

Retire the duplicate `Sheaf.Topology.StalkDirectSums` in favor of its adopted
source twin, as requested by the 2026-10-20 retirement hand-off. The source theorem
has the identical conclusion and germ formula, and drops only the unused sectionwise
commutativity hypothesis. A scratch example proves the complete old signature by
`exact SheafOfModules.exists_stalk_directSum_linearEquiv R I F x` after importing
only the upstream twin. Its axiom check reports `propext`, `Classical.choice`, `Quot.sound`.
The source file, its declarations, signatures, attributes, public imports and proofs
are all preserved verbatim.

## Old

The duplicate module declared:

```lean
theorem exists_stalk_directSum_linearEquiv {X : TopCat.{u}} (R : X.Sheaf RingCat.{u}) (I : Type u) (_hcomm : ∀ (U : Opens X) (r s : R.obj.obj (op U)), r * s = s * r) (F : I → SheafOfModules.{u} R) (x : X) : ∃ e : (stalk (C := AddCommGrpCat.{u}) (X := X) (∐ F).val.presheaf x) ≃ₗ[stalk (C := RingCat.{u}) (X := X) R.obj x] (⨁ i : I, (stalk (C := AddCommGrpCat.{u}) (X := X) (F i).val.presheaf x)), ∀ (i : I) (U : Opens X) (hx : x ∈ U) (s : (F i).val.obj (op U)), e (germ (∐ F).val.presheaf U x hx ((Sigma.ι F i).val.app (op U) s)) = DirectSum.lof (stalk (C := RingCat.{u}) (X := X) R.obj x) I (fun j : I => ↑(stalk (C := AddCommGrpCat.{u}) (X := X) (F j).val.presheaf x)) i (germ (F i).val.presheaf U x hx s)
```

Its direct consumer had `import Sheaf.Topology.StalkDirectSums`.

## New

Withdraw `lean/Sheaf/Topology/StalkDirectSums.lean` via `deleted.txt`, and point
`lem-pc-stalk-direct-sums` to the existing source declaration:

```lean
theorem exists_stalk_directSum_linearEquiv {X : TopCat.{u}} (R : X.Sheaf RingCat.{u}) (I : Type u) (F : I → SheafOfModules.{u} R) (x : X) : ∃ e : (stalk (C := AddCommGrpCat.{u}) (X := X) (∐ F).val.presheaf x) ≃ₗ[stalk (C := RingCat.{u}) (X := X) R.obj x] (⨁ i : I, (stalk (C := AddCommGrpCat.{u}) (X := X) (F i).val.presheaf x)), ∀ (i : I) (U : Opens X) (hx : x ∈ U) (s : (F i).val.obj (op U)), e (germ (∐ F).val.presheaf U x hx ((Sigma.ι F i).val.app (op U) s)) = DirectSum.lof (stalk (C := RingCat.{u}) (X := X) R.obj x) I (fun j : I => ↑(stalk (C := AddCommGrpCat.{u}) (X := X) (F j).val.presheaf x)) i (germ (F i).val.presheaf U x hx s)
```

The direct consumer now has `import WeilConjectures.Topology.StalkDirectSums`.
This is a private proof import, so the consumer's exported interface is unchanged.
No theorem call site in the current downstream closure uses the old extra binder.
The node's mathematical statement and categorical proof route remain unchanged.

## Users

`tools/downstream.py Sheaf.Topology.StalkDirectSums --uses
SheafOfModules.exists_stalk_directSum_linearEquiv` finds three downstream modules,
and no downstream theorem call sites. The retirement inventory also names the
old Sheaf supported-detector module, which is already absent from the current tree;
its current upstream replacement imports the source twin directly.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.Topology.StalkDirectSums | U4 | Withdraw duplicate; record source theorem. |
| Sheaf.AlgebraicGeometry.ConormalGradedAlgebra | unclaimed | Replace one proof import; all declarations unchanged. |
| Sheaf.AlgebraicGeometry.ConormalGradedAlgebraHomExt | unclaimed | No edit; compile against adapted consumer. |
| Sheaf.AlgebraicGeometry.ConormalAlgebraFlatBaseChange | M7 | No edit; compile against adapted consumer. |
| WeilConjectures.AlgebraicGeometry.SupportedCompactDetectorModel | unclaimed | No edit; already calls source theorem with R I M y. |

No target statement or definition changes meaning. The source theorem covers
arbitrary rings and arbitrary index types (including empty types), so it includes
every case of the retired theorem.

## Status

landed 20261020T144306-L-2262661 2026-10-20 (merge of deliver/U4/Sheaf.Topology.StalkDirectSums)
