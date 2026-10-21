# AlgebraicGeometry.Scheme.nonempty_equiv_twoCocycleClasses_cohomologicalBrauerGroup

## Reason

The item is listed in coord/retire-items.tsv. The Sheaf theorem has zero direct
holes and duplicates the adopted source construction
`AlgebraicGeometry.Scheme.twoCocycleClassesEquivCohomologicalBrauerGroup`.
The source constructs the equivalence directly; the Sheaf proof obtains two
embeddings and applies Schroeder-Bernstein before composing equivalences.
Retire this duplicate and preserve its node through the existing construction.

## Old

```lean
theorem nonempty_equiv_twoCocycleClasses_cohomologicalBrauerGroup
    (K : Type u) [Field K] :
    Nonempty (Field.GaloisUnitsTwoCocycleClasses K ≃
      (Spec (.of K)).CohomologicalBrauerGroup)
```

## New

Withdraw `Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison` through
deleted.txt. Attach its existing node to the unchanged source declaration:

```lean
noncomputable def twoCocycleClassesEquivCohomologicalBrauerGroup (K : Type u) [Field K] :
    Field.GaloisUnitsTwoCocycleClasses K ≃ (Spec (.of K)).CohomologicalBrauerGroup
```

The exact old theorem, including its universe and all hypotheses, follows by:

```lean
  exact ⟨twoCocycleClassesEquivCohomologicalBrauerGroup K⟩
```

This was compiled through lcompile.py in scratchpad/OldStatement.lean (2.3 s).
Both the old statement proved this way and the source construction have only
propext, Classical.choice and Quot.sound among their axioms. The construction
applies to every field, including imperfect fields and positive characteristic;
no separability or algebraic-closedness hypothesis on K is added. The quotient
and the cohomological Brauer group are exactly the original types.

The node's Lean attachment and proof fields now describe the source composite:
inverse homogeneous cocycle descent followed by inverse additive etale/Galois
comparison, forgetting additivity. Its mathematical statement and statement
dependencies stay unchanged. No source-library file is edited.

## Users

Current whole-library import and declaration searches find no consumer. The
listed inventory consumer, Sheaf.AlgebraicGeometry.EtaleGaloisUnitsComparison,
has already been retired to an empty module by N3. A fresh
`tools/downstream.py ... --direct` reports zero direct importers. The `--uses`
search finds the old name only in the item itself. Searches of quarantine find
neither the import nor an application of the old declaration.

| module | group holding it | effect |
| --- | --- | --- |
| Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison | J1 | Retire the duplicate. |

There are no active DAG parents: scanning every node's stmt_deps, proof_deps and
proof-step uses finds no reference to this node. The references from other
nodes are historical blueprint ancestry or provenance, not proof dependencies.
No unit realization cites it; sk-thm-br and its route remain unchanged. The node
is retained and attached to the source, so future users retain the same fact.

## Status

landed 20261021T013816-L-2338830 2026-10-21 (merge of deliver/J1/Sheaf.AlgebraicGeometry.EtaleUnitsTwoCocycleComparison)
