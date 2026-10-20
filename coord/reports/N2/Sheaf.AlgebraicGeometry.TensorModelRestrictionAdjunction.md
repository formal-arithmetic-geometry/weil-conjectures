## What changed

Restored `Sheaf.AlgebraicGeometry.TensorModelRestrictionAdjunction` from its
quarantine archive and repaired its public imports. Replaced the withdrawn
`Sheaf.AlgebraicGeometry.DerivedTensorAugmentation` import with direct imports of
`Sheaf.Algebra.Homology.KFlat` and
`WeilConjectures.AlgebraicGeometry.DerivedTensorStructure`. Retained the upstream
internal-Hom import and the two private proof imports.

The public theorem `AlgebraicGeometry.Scheme.exists_tensorModel_restriction_adjunction`
and both private helpers retain their exact archived signatures and proofs.
The proof still transports the canonical tensor-Hom equivalences along the
coherent comparison isomorphisms, then proves restriction compatibility and
naturality by the comparison equations. No DAG route changes or new nodes.

Validation: the restored theorem signature matches its DAG record exactly;
all lines are within 100 columns. The delivery dry run passed compilation, axiom
probes and server preflight. Public-import replacement is classified CODEX for
the maintainer's independent review.

Change record:
`coord/changes/tensor-model-restriction-adjunction-rework-20261020.md`.

## Proved and sorry left

This is an import repair with zero original holes. Holes closed: none (0 of 0).
Holes added: none. Holes left in the item: none. Both private helpers and
`AlgebraicGeometry.Scheme.exists_tensorModel_restriction_adjunction` have complete
proofs. No decomposition or split-off statement.

The sandbox also contains the byte-identical current source of
`Sheaf.AlgebraicGeometry.TensorModelRestrictionComparisons`, whose imports were
already repaired and landed by D3. Recompiling it supplies the repaired artifact;
it creates no delivery diff and has zero holes.

## No longer needed

Removed the public import of
`Sheaf.AlgebraicGeometry.DerivedTensorAugmentation`: the theorem never uses an
augmentation or `IsDerivedTensorAugmentation`; it only needs the K-flat predicate
and derived tensor infrastructure now imported directly. That module is already
withdrawn. No new module is pruned or withdrawn by this delivery.

Retained both declared proof dependencies:
`lem-sc-tensor-model-restriction-comparisons` and
`def-pc-canonical-derived-tensor-hom-bijection`. The canonical tensor-Hom module
remains a private proof import. No unit-level statement or proof step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The generic brief describes an item with `sorry`; this current rework assignment
has none. Its actual defect is the upstream-sync import conflict recorded in
`coord/rework.tsv`. The quarantine archive and its Lean attachment are preserved.
The upstream theorem has the same name but spells its K-flat predicate
`IsKFlatTensor`; the assigned archived interface uses `IsAcyclicTensorKFlat`.
This repair preserves that interface and its existing proof rather than changing
the recorded declaration.

The first compile with repaired direct imports still encountered the duplicate
internal-Hom declaration through the published comparison artifact. Compiling the
already landed comparison source and the item together resolved that conflict;
each compiled within 24 seconds. The comparison source is unchanged.

Read the Stacks source at equation-internal-hom and lemmas internal-hom and
restriction-RHom-to-U (Tags 08DJ and 08DL). The proof uses their existing coherent
comparison interface exactly as the DAG records. Search checks used LeanFinder
(tensor-Hom adjunction under open restriction), Loogle (`Iso.homCongr`), and grep
(`homCongr|tensorHom_precomp`); the generic transport APIs support the retained
proof. A full source import-closure check found no remaining path from its three
main dependencies to `Sheaf.Algebra.Homology.DerivedInternalHom`.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
