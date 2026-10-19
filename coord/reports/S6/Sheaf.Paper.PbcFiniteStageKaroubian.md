## What changed

Replaced the sole `sorry` in
`AlgebraicGeometry.Scheme.finite_stage_karoubian` with the stated three-step argument.
Obtain the rational t-structure from `pbc_localized_tstructure T l E`, turn
`t.bounded = ⊤` into objectwise boundedness, and apply
`TStructure.isIdempotentComplete_of_bounded` and
`TStructure.isEquivalence_toKaroubi_and_isTriangulated_of_bounded`.
The triangulated structure is the existing localized structure on the same raw category.
The Tor-dependent truncation formula is not used.

Only `lean/Sheaf/Paper/PbcFiniteStageKaroubian.lean` changes. The statement,
public imports, docstrings, and definitions are unchanged. The proof follows the
existing node and its current blueprint update, so no node update is necessary.
The assigned module compiled cleanly with `lcompile.py` (4.1 seconds).

## Proved and sorry left

Closed 1 hole: `AlgebraicGeometry.Scheme.finite_stage_karoubian`
(node `thm-weil-pbc-finite-stage-karoubian`).
Added 0 holes. There are no remaining `sorry`s in the delivered module.
No statements are split off. This proves the item from its declared dependencies;
it does not assert that every transitive dependency is already free of `sorry`.

## No longer needed

None. Every declared proof dependency is retained: the raw rational category,
its localized bounded t-structure, and the general bounded-t-structure Karoubian theorem.
The existing proof-only import of
`WeilConjectures.CategoryTheory.Idempotents.TStructure` is used directly.
The public imports supply the statement's category, coefficient data, and triangulation.
No imports, nodes, or modules are pruned.

## Where the brief, the DAG or earlier work was wrong

No mathematical or interface discrepancy was found. The current blueprint places
this theorem under `sk-thm-sbc-karoubian`, whereas the existing node and docstring retain
its older `sk-rem-rest` source path; its current proof and the node's blueprint update
both prescribe the bounded-t-structure argument implemented here.
The analogous library proof `WeilConjectures.rationalization_idempotent_complete`
confirms this pattern but concerns a different coefficient category and is not imported.

## Second reading by S6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
