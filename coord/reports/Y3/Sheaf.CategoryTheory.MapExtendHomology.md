## What changed

Replaced the private `mapExtendTermIso`, `mapExtendTermIso_comm`, and
`mapExtendComplexIso` with the existing `HomologicalComplex.mapExtendIso`, imported
from `WeilConjectures.FromJoel.Algebra.Homology.Embedding.ExtendMap` as a proof-only
import. The public theorem `mapExtendHomology_nonempty_iso` retains its exact
signature. Its proof maps the complex isomorphism through degree-q homology and
composes with `HomologicalComplex.extendHomologyIso`.

The second reading removed two redundant public imports:
`Mathlib.Algebra.Homology.Embedding.CochainComplex` and
`Mathlib.Algebra.Homology.HomologicalComplexAbelian`. The remaining public import
`Mathlib.Algebra.Homology.Embedding.ExtendHomology` supplies the public signature's
complex, extension, abelian-category and homology infrastructure transitively.
No public definition or statement changed. The private duplicate removal is already
documented by the repository's landed `coord/changes/map-extend-homology.md`.

## Proved and sorry left

`mapExtendHomology_nonempty_iso` (node `lem-weil-pbc-map-extend-homology`) is fully
proved. It was already proved in the repository version: holes closed = 0; holes
added = 0. No split-off statements, no remaining `sorry`, and no hollow definitions.
This delivery repairs duplicates and prunes imports; it claims no net proof-hole
progress. All three private helpers removed were also already proved.

Local compilation succeeds. A scratch copy with `#print axioms` for the public
theorem, `HomologicalComplex.mapExtendIso`, and
`HomologicalComplex.extendHomologyIso` reports only `propext`, `Classical.choice`,
and `Quot.sound`.

## No longer needed

Removed direct imports:
- `Mathlib.Algebra.Homology.Embedding.CochainComplex`
- `Mathlib.Algebra.Homology.HomologicalComplexAbelian`

Removed duplicate private helpers: `mapExtendTermIso`, `mapExtendTermIso_comm`,
`mapExtendComplexIso`. The node's old `proof_deps` is empty; no dependency nodes
need removal. No Sheaf or WeilConjectures module is claimed pruned from the target
closure.

## Where the brief, the DAG or earlier work was wrong

The initial report understated the changes: relative to the repository this removes
three private duplicates and adds a proof-only upstream import. The repository's
theorem was already proved; this is the duplicate repair listed in coord/repairs.txt,
not a newly closed hole. The existing DAG proof and proof_origin already describe
the canonical upstream argument and need no edits.

## Second reading by Y3

1. Compared the whole delivered module with the repository using diff. The sole
   public theorem's signature is byte-for-byte unchanged, including the independent
   universes of both abelian categories, additivity, arbitrary natural-indexed K,
   arbitrary natural q, and the Nonempty isomorphism conclusion. Only private
   duplicates, imports, the proof, and its explanatory docstring differ. No data
   definition or target statement changes.
2. Compiled the delivered module locally without errors or warnings. Read the
   upstream mapExtendIso construction and the Mathlib extendHomologyIso definition.
   The composition has precisely the required source and target. Explicit scratch
   axiom checks give only the three allowed axioms, with no sorryAx. No forbidden
   declarations or sorry occur in the delivered source.
3. No new or split-off statement exists, so no new node, search obligation, or
   unproved witness is introduced. For q=0 the extension homology theorem includes
   the zero incoming differential; for q>0 it identifies the same three terms.
   Zero complexes and zero additive functors also satisfy the construction. No
   exactness of E is assumed or used.
4. The canonical proved upstream isomorphism is the shortest existing route and
   replaces the duplicate componentwise argument. Inspected dag/units/sk-thm-p1.json:
   this auxiliary node is below its realized statement and steps, none of which
   changes or is bypassed. The original proof_deps is empty. Tested removal of each
   redundant import separately and both together; the reduced file compiles.
   The upstream import is correctly proof-only. No additional pruning is claimed.
5. Read lem-weil-pbc-map-extend-homology.json: its two proof steps describe exactly
   mapExtendIso followed by homologyFunctor.mapIso and extendHomologyIso;
   proof_deps is empty, and proof_origin names both source declarations. The Lean
   statement matches the node, including q=0 and absence of an exactness hypothesis.
   No DAG edit is necessary.

Second reading changed the report to describe the actual duplicate repair and
zero hole delta, and removed the two redundant public imports. The proof itself
needed no repair.

Public-import pruning change record: `coord/changes/map-extend-homology-import-pruning.md`.
The dry run required this record because public import removal changes exported
visibility. It records all 215 downstream modules; none needs adaptation.

Downstream validation: the sole direct importer was compiled unchanged against the
sandbox's reduced module in a scratch overlay, successfully in 56.0 seconds. An
initial overlay run timed out at 60 seconds; the original against the published
library took 59.1 seconds. This confirms it is near the existing compile budget,
with no adaptation required. The delivered module itself compiles in a few seconds.
