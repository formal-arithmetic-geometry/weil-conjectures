## What changed
The target theorem now handles the empty open subscheme directly and reduces the nonempty case to the new theorem `exists_local_normal_form_of_constantRank_nonempty`. The new theorem is in `ConstantRankMapNormalFormNonempty.lean`.

## Proved and sorry left
The empty-subscheme branch of `exists_local_normal_form_of_constantRank` is proved. The nonempty theorem `exists_local_normal_form_of_constantRank_nonempty` remains `sorry` (node `lem-pc-constant-rank-map-local-normal-form-nonempty`).

## No longer needed
None.

## Where the brief, the DAG or earlier work was wrong
The original proof plan does not provide Lean-level affine minor lemmas; the nonempty reduced-affine argument is split into a named intermediate theorem.

## New nodes
`lem-pc-constant-rank-map-local-normal-form-nonempty` records the nonempty-case intermediate theorem.

## Second reading by K2

1. I compared both delivered modules with the repository versions. The existing parent theorem signature is byte-for-byte unchanged; the only parent changes are the proof and a proof-only import. The new module and node are additional files.
2. Both modules compile with `lcompile.py`; no forbidden declarations occur. The parent closes its empty-subscheme branch, while the nonempty theorem remains the single named `sorry` listed above. The proof uses no new axioms beyond the permitted baseline.
3. The nonempty statement is a strict intermediate case with the explicit `[Nonempty Z]` hypothesis, and its docstring gives the source and the complete reduced-affine minor argument. The node now records the exact declaration name and matching statement.
4. The proof follows the unit route: it reduces the parent to the nonempty reduced-affine normal-form argument and proves the empty case directly. No imports or nodes were pruned.
5. DAG metadata now matches the Lean declaration, proof steps, and proof dependencies; the unit and existing target node remain unchanged.

I changed the nonempty theorem docstring, corrected its node declaration and statement metadata, replaced the circular node proof sketch with the actual minor-argument steps, and added this second-reading record.
