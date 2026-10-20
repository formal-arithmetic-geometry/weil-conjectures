## What changed

Retired `Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration` through `deleted.txt`.
Redirected `split-locally-constant-cover-filtration` to the existing same-named theorem
`AlgebraicGeometry.Scheme.IsFiniteLocallyConstantSheaf.exists_finite_etale_cover_filtration_sheaf`
in `WeilConjectures.ConstructibleSheaf.LocallyConstantCoverFiltrationExtension`.
The full signatures are byte-for-byte identical. This completes the retirement listed in
`coord/retire-items.tsv`, rather than attempting another decomposition of the theorem.
Change record: `coord/changes/J7-retire-locally-constant-cover-filtration.md`.

The original item, the source replacement, and the sole DAG parent
`WeilConjectures.ConstructibleSheaf.LocallyConstantReduction` each compile through
`lcompile.py` (3.6 s, 4.8 s and 3.6 s respectively). No source module is changed.
The parent already imports the replacement and applies exactly its theorem, so no consumer
adaptation is needed. No Lean module imports the retired copy (`downstream.py`: zero).

## Proved and sorry left

Zero direct holes before, zero after; zero holes closed and zero holes added.
No theorem is newly proved and no statement is split off. The existing proved declaration
is retained in its source module; this is duplicate retirement, not proof progress.
The existing Sylow-cover, categorical-flag and invariant-flag dependencies are retained.
No remaining sorry is introduced or moved by this delivery.

## No longer needed

Pruned module: `Sheaf.ConstructibleSheaf.LocallyConstantCoverFiltration`.
Its two public imports and three private proof imports disappear with the redundant copy;
the source replacement keeps its own existing imports. No mathematical dependency node
is pruned: the Sylow cover, invariant flag, and categorical realization remain necessary
and remain in the node's proof_deps. The sole actual DAG parent is
`lemma-weil-pbc-curve-locally-constant-reduction`; its node reference is preserved and now
points to the canonical source declaration through the repaired attachment.
The unit `sk-thm-p1` and all its realized steps are unchanged.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes an unfinished proof, but the current item already has
zero direct sorries. Its actual assignment is the retirement row. That row says the nominal
twin `WeilConjectures.ConstructibleSheaf.LocallyConstantCoverFiltration` lacks the `_sheaf`
declaration; the exact declaration is present in the source's `LocallyConstantCoverFiltrationExtension`.
The node still pointed to the redundant Sheaf copy even though its sole parent had already
migrated to the source Extension. The attachment is now reconciled with that parent.

Checked the two statements in full: hypotheses, universes, geometric-fibre cardinalities,
zero initial object, endpoint isomorphism, monomorphisms and constant cokernels all match.
Consequently zero sheaves and filtration length zero have exactly the same behavior.
The retained proof still uses the Sylow cover and p-group filtration, so there is no change
to the unit route. Loogle found no match for `"filtration", "Sheaf"`; LeanFinder returned
unrelated locally constant module results; msearch grep found no Mathlib theorem.
Local source search found the exact source Extension used for this retirement.
Search records are in the sandbox's `searches.jsonl`.

## Second reading by J7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
