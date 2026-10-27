# WeilConjectures.podCtfAdjunctions_exists

## Reason

Prune an unused auxiliary existence assertion in the assigned Sheaf module.
The actual node theorem podGeneralCtfAdjunctions is already proved, with its
three ambient-compatible restrictions. Every Lean Hom-chain consumer supplies
PodCtfAdjunctionData as a parameter; none obtains that data from this existence
assertion. The earlier independent review recorded the same unused-theorem
finding in reviewed_lean of det-thm-sf-ctf-stability-adjunctions.

Checked all eight downstream modules with tools/downstream.py --uses, all Lean
sources, all DAG references, all unit records, and the quarantine Lean sources.
The only Lean occurrence of the removed name is its own declaration. The DAG
parents use the explicit data, its constructed restricted adjunctions, or the
general mathematical restriction theorem. They do not use this extra assertion
about an arbitrary SixFunctorOperationDatum. The node and all its parent edges
stay: this is declaration-level pruning, not withdrawal of the node or module.

## Old

```lean
theorem podCtfAdjunctions_exists
    {D : FiniteFieldDatum.{u}} {C : D.CoefficientDatum}
    {E : Type u} [Field E] [Algebra (Padic C.l) E]
    [FiniteDimensional (Padic C.l) E] {n : ℕ} {hn : 1 ≤ n}
    (S : SixFunctorOperationDatum D C E n hn) (s : PodCoefficientStage)
    {X Y : SixFunctorSpace D} (f : X ⟶ Y)
    [IsSeparated f.hom.left] [LocallyOfFiniteType f.hom.left] [QuasiCompact f.hom.left]
    (c : Compactification f.hom.left) :
    Nonempty (PodCtfAdjunctionData (PodCoefficientStage.operations S s)
      (PodCoefficientStage.domain S s) (PodCoefficientStage.homPairs (S := S) s)
      (PodCoefficientStage.internalHom (S := S) s) (PodCoefficientStage.tensor S s) f c)
```

## New

Removed. PodCtfAdjunctionData, all its definitions and the proved
podGeneralCtfAdjunctions retain their signatures and all mathematical content.
Its proof now directly invokes compactification_coherence_cocycle with the
current explicit ground-field argument, removing the obsolete fallback that
the compiler flags as unreachable. All retained definition bodies are verbatim. No replacement theorem or hypothesis
is introduced. Remove only this auxiliary name from the node's lean.declarations.
The node statement and proof dependencies are unchanged. No target definition
or statement changes, so no target meaning review is reopened.

## Users

| module | group holding it | effect |
|---|---|---|
| Sheaf.Paper.PodCtfAdjunctions | T2 | Remove unused auxiliary theorem; retain the explicit data and proved general theorem. |
| Sheaf.Paper.CoefficientGammaRepresentatives | unclaimed | Does not use the removed theorem; no adaptation. |
| Sheaf.Paper.HomChainPairingNaturality | unclaimed | Does not use the removed theorem; no adaptation. |
| Sheaf.Paper.PodCtfPairingMaps | unclaimed | Does not use the removed theorem; no adaptation. |
| Sheaf.Paper.PodHomChainCounitFormula | H1 | Does not use the removed theorem; no adaptation. |
| Sheaf.Paper.PodHomChainCtfDomains | unclaimed | Does not use the removed theorem; no adaptation. |
| Sheaf.Paper.PodHomChainUncurriedTransport | unclaimed | Does not use the removed theorem; no adaptation. |
| Sheaf.Paper.TensorHomCoefficientTransposes | unclaimed | Does not use the removed theorem; no adaptation. |
| Sheaf.Paper.VerdierHomChainComposition | N3 | Does not use the removed theorem; no adaptation. |

No other module is adapted, including modules held by other groups. The source
library under WeilConjectures is untouched.

## Status

landed 20261025T203212-L-2791315 2026-10-25 (merge of deliver/T2/Sheaf.Paper.PodCtfAdjunctions)
