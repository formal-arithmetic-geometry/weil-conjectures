## What changed

Proved `Matrix.exists_standardCover_idempotentCharpoly_eq_charpoly` in
`Sheaf.LinearAlgebra.IdempotentCharpolyLocalCharpoly`, preserving its signature,
visibility, docstring, and public imports. The proof uses the finite-projective
standard free cover of the projector image, its image-base-change equivalence,
and rectangular determinant compression. Zero localizations use the empty matrix.

Repair of both duplicate-theorem findings: removed the private declarations
`Matrix.idempotentCharpoly_map` and `Matrix.idempotentCharpoly_reindex`.
The existing names in `Sheaf.RingTheory.AdjoinRootIdempotentCharpolyMap` are private,
so importing that module cannot make them accessible. Instead, the calculation uses
Mathlib's existing general theorems `RingHom.map_det`, `Matrix.charmatrix_map`,
`Matrix.charmatrix_reindex`, and `Matrix.det_reindexAlgEquiv` directly on the defining
polynomial matrix. No replacement mapping or reindexing theorem is declared, and no
other module or interface is changed. The proved private rectangular-retract helper
remains. Updated the DAG calculation step and proof origin accordingly.

Added proof-only imports of `Mathlib.RingTheory.Localization.BaseChange`,
`Mathlib.LinearAlgebra.Matrix.SchurComplement`, and
`Mathlib.LinearAlgebra.FreeModule.StrongRankCondition` for the implemented proof.

## Proved and sorry left

Closed the one original hole:
`Matrix.exists_standardCover_idempotentCharpoly_eq_charpoly`
(node `lem-weil-pbc-idempotent-charpoly-local-charpoly`).
There are no remaining `sorry`s in the item and none added elsewhere. No holes were
split off. The retained private helper `Matrix.idempotentCharpoly_retract` is proved.
The two Sheaf proof dependencies are already proved in the baseline. Single-file
compilation succeeds without warnings; the delivery dry run checks declaration axioms.

## No longer needed

Removed duplicate private declarations `Matrix.idempotentCharpoly_map` and
`Matrix.idempotentCharpoly_reindex`; Mathlib's general determinant results suffice.
No original imports, dependency nodes, or modules were removed: the finite-projective
standard cover, image-base-change, and determinant definition are all used.
`Sheaf.RingTheory.AdjoinRootIdempotentCharpolyMap` is not needed as an import: its
relevant helpers are private, and its public CRT specialization is not used here.
The plan's second cover for 1-P, pairwise product refinement, complementary basis,
invertible conjugation, and block diagonalization are unnecessary. No new modules
or nodes for those steps are delivered. The unit's realized statements and steps
remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned delivery duplicated two private facts already proved in
`Sheaf.RingTheory.AdjoinRootIdempotentCharpolyMap`. Both duplicate declarations have
been removed. The repair uses the general Mathlib determinant theorems directly,
avoiding an interface change just to expose another module's private helpers.
The earlier second-reading record described the superseded delivery and has been
removed; the repair requires a fresh second reading.

No false statement was found. A single locally free image and rectangular determinant
compression replace the longer complementary-basis route. The commuting hypothesis
is unnecessary for this argument but is retained verbatim. The original docstring
gives a valid longer proof plan; the DAG records the implemented shorter route.

## Second reading by T2

1. **Signatures and visibility.** Compared the delivered module with the repository version. The theorem signature, visibility, definitions, and existing declarations are unchanged; only proof-only imports and proofs differ. The DAG node's Lean statement matches the declaration byte for byte.
2. **Proof and axioms.** Compiled the module with `lcompile.py`; it succeeds without errors or warnings. The file contains no `sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`. The proof uses the finite-projective standard cover, image base change, and Mathlib determinant functoriality. The zero-ring branch is handled by subsingleton equality, and empty index sets use the same finite-basis construction.
3. **Statements and duplication.** The target statement is unchanged and retains the commuting hypothesis. The private rectangular retract helper is a strict intermediate calculation, not a restatement of the target. The removed private map and reindex helpers duplicated general Mathlib results; no new split-off statements or holes were added.
4. **Pruning and imports.** The three added imports are proof-only and used by the implementation. The former adjoin-root import and complementary-basis route are unnecessary. The finite-projective cover and image-base-change dependencies remain in the proof and node. The unit's realized statement and route are preserved.
5. **DAG agreement.** Updated proof steps, proof dependencies, and proof origin describe the implemented rectangular-retract route and direct Mathlib mapping/reindexing lemmas. No statement or definition node was changed.

I changed only this review record; no Lean declarations or target statements were altered.
