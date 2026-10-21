# AlgebraicGeometry.Etale.boundaryOmegaT

## Reason

Factor the canonical etale construction through `CategoryTheory.BoundaryData` and
its explicit functor interfaces. This keeps the actual functors and maps while making
kernel conversion tractable. The independent Hom chain remains independent of alpha;
alpha remains the tensor-Hom transpose of the specified q/r/evaluation pairing.
No source-library declaration is changed and no arbitrary existence witness is chosen.
The public theorem retains the original hypotheses and all three conclusions, factored
through an explicit proposition definition. Definitions used by the targets
have changed implementation, so their statement-meaning review must be reopened.

## Old

```lean
noncomputable def boundaryOmegaT {k : Type u} [Field k] (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT] :=
  dualizingComplex (ModuleCat.{u + 1} A) aT
```

## New

```lean
noncomputable def boundaryOmegaT {k : Type u} [Field k] (aT : T ⟶ Spec (.of k))
    [IsSeparated aT] [LocallyOfFiniteType aT] [QuasiCompact aT] :
    (DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :=
  dualizingComplex (ModuleCat.{u + 1} A) aT
```

## Users

There are no current downstream textual users of these definitions according to
`tools/downstream.py --uses`. The pending parent is quarantined at
`quarantine/Sheaf/SixFunctors/BoundaryDualityDischarge.lean` (recorded in coord/rework.tsv),
and is unclaimed. It imports this item but does not mention the changed definitions.
Its DAG attachment and proof dependencies remain intact.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.SixFunctors.BoundaryAlphaNormalization | C6 | Canonical formulas factored through real categorical constructions. |
| Sheaf.SixFunctors.BoundaryDualityDischarge | unclaimed; quarantined | Same hypotheses and conclusions; no direct uses of the changed declarations. |

## Status

landed 20261021T005730-L-1886275 2026-10-21 (merge of deliver/C6/Sheaf.SixFunctors.BoundaryAlphaNormalization)
