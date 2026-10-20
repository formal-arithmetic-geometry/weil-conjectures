# CategoryTheory.discreteContAction_finite_orbit_coproduct

## Reason

Complete the retirement assigned in `coord/retire-items.tsv`, under the human's
2026-10-20 retirement instructions in `retire-sheaf-twins-20261020.md`.
The Sheaf module duplicates the complete upstream orbit-coproduct theorem with
identical binders and conclusion. Retire the copy, redirect its one direct
consumer, and attach its DAG node to the upstream theorem. No upstream file changes.

## Old

`lean/Sheaf/CategoryTheory/DiscreteContActionFiniteOrbitCoproduct.lean` declares:

```lean
theorem discreteContAction_finite_orbit_coproduct
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] (M : DiscreteContAction (Type w) G) :
    let U := ObjectProperty.ι (ContAction.IsDiscrete (V := Type w) (G := G))
      ⋙ ObjectProperty.ι (Action.IsContinuous (V := Type w) (G := G))
      ⋙ Action.forget (Type w) G
    ∃ (I : Type w) (A : I → DiscreteContAction (Type w) G) (f : ∀ i, A i ⟶ M),
      (∀ i, Finite (A i).obj.obj.V) ∧
      Nonempty (IsColimit (Cofan.mk M f)) ∧
      Nonempty (IsColimit (U.mapCocone (Cofan.mk M f)))
```

Its sole direct consumer has the private proof import:

```lean
import Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct
```

## New

The duplicate module is withdrawn via `deleted.txt`. The identical declaration
already exists, completely proved, in
`WeilConjectures.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct`.
The consumer's only changed line is:

```lean
import WeilConjectures.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct
```

The DAG node's `lean` record now names that existing source module and declaration.
Its statement, proof plan, dependencies and audit fields are preserved.

The current copy, after the intervening A9 landing, publicly imports
`WeilConjectures.AlgebraicGeometry.EtaleFieldGsets` and registers the existing
`AlgebraicGeometry.etaleFieldDiscreteForget₂` and
`AlgebraicGeometry.etaleFieldActionForget₂` globally. The upstream orbit file
imports `WeilConjectures.AlgebraicGeometry.EtaleFieldGeometricAction` and uses
those same instances locally. Retiring the copy removes its registrations;
the consumer needs neither registration: its exact original statement and proof
compile unchanged after replacing the private import (server: 1.3 s).
A temporary check compiled the current copy's statement verbatim as an example
proved by the upstream theorem, with the upstream instances enabled locally
(server: 1.3 s). Its axiom check reports only `propext`, `Classical.choice`,
and `Quot.sound`. The temporary file is not part of the delivery.

This packet repairs the failed landing of reviewed head `a8f2406646`:
the consumer and DAG node were reread from current sheaf-dag, with only the
private import and Lean attachment changed. The current item is still the
same complete theorem, and is withdrawn under the reviewed retirement request.
No prior A9 change is undone or copied back from the old delivery base.

## Users

`tools/downstream.py --direct --uses discreteContAction_finite_orbit_coproduct`
finds one direct consumer and no external textual use of the theorem. The full
transitive scan finds the following three modules; all are unclaimed in the
coordination snapshot. The replaced import is private, so it does not change
what the two indirect consumers see.

| module | group holding it | effect |
|---|---|---|
| Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct | Y3 | Retire duplicate and redirect node to upstream. |
| Sheaf.RepresentationTheory.NormalSubgroupIndUnipotence | unclaimed | Replace one private import; all declarations unchanged; compiled on the server in 1.3 s. |
| Sheaf.AlgebraicGeometry.GaloisPartitionExactRefinement | unclaimed | Indirect consumer; source unchanged; compiled against adapted consumer (2.1 s). |
| Sheaf.Paper.CtfHomLocallyConstant | unclaimed | Indirect consumer; source unchanged; compiled against adapted consumer (2.2 s). |

The source import closure scan finds no newly co-visible Sheaf/upstream twin
pairs. No source module imports the withdrawn module after the consumer edit.
No definition or target statement changes; target meanings are unchanged.

## Status

landed 20261020T153027-L-2865282 2026-10-20 (merge of deliver/Y3/Sheaf.CategoryTheory.DiscreteContActionFiniteOrbitCoproduct)
