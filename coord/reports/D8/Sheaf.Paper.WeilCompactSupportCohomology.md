## What changed

Filled thirteen of the sixteen theorem holes in
`Sheaf.Paper.WeilCompactSupportCohomology`, without changing any declaration,
definition, signature, or visibility. Added the proof-only import
`Mathlib.Algebra.CharP.CharAndCard` for the cardinality/characteristic criterion.
The compactification structure
properties follow from composition and the given proper/open factors. The open
factor equation follows from `Compactification.comm` and `Over.w`. Geometric
structure properties follow from pullback projection instances; properties of the
base-changed morphism use `MorphismProperty.overPullbackMap`. The source structure
properties follow from composition after rewriting by `Over.w`.

`zlClosurePrimeUnit` now derives the characteristic of the finite base field from
its cardinality, transfers that characteristic to its algebraic closure using the
injective algebra map, and applies `CharP.isUnit_natCast_iff` and distinctness of
the primes. This proof does not import a duplicate prime-invertibility theorem
whose proof remains open.

## Proved and sorry left

Closed 13 existing holes, all in node
`def-zl-weil-compact-support-cohomology`:

- `WeilConjectures.zlCompactificationMiddle_finiteType`
- `WeilConjectures.zlCompactificationMiddle_quasiCompact`
- `WeilConjectures.zlCompactificationOpen_w`
- `WeilConjectures.zlCompactificationOpen_isOpenImmersion`
- `WeilConjectures.zlGeometricFiber_finiteType`
- `WeilConjectures.zlGeometricFiber_quasiCompact`
- `WeilConjectures.zlFiberMap_isOver`
- `WeilConjectures.zlFiberMap_separated`
- `WeilConjectures.zlFiberMap_finiteType`
- `WeilConjectures.zlFiberMap_quasiCompact`
- `WeilConjectures.zlClosurePrimeUnit`
- `WeilConjectures.zlSource_finiteType`
- `WeilConjectures.zlSource_quasiCompact`

Three existing holes remain unchanged, all in the same node:

- `WeilConjectures.zlWeilHigherShriek_representable`
- `WeilConjectures.zlWeilHigherShriek_compactification_independent`
- `WeilConjectures.zlWeilHigherShriek_compactSupportComparison`

Validation: rechecked the retained proof against current shared sources on
2026-10-19. The final module compiles cleanly on the project server in 7.8 s
(and 10.1 s in the import-order axiom check).
An import-order compile of the module followed by a temporary axiom probe confirms
that each of the thirteen completed declarations uses only `propext`,
`Classical.choice`, and `Quot.sound`; none uses `sorryAx`. The temporary probe was
removed from the sandbox before delivery.

Added zero holes; split off zero theorems. This is a partial proof delivery,
not a decomposition. The remaining theorems retain their existing complete
natural-language proof docstrings and node attachment.

## No longer needed

None. All four original public imports are needed by the existing statements
and definitions. No proof dependency, node, or module is pruned. The original
node has empty `proof` and `proof_deps`; no declared route is bypassed. The unit's
statement and route are unchanged. A trial explicit import of
`Mathlib.Algebra.CharP.Invertible` was removed because the existing imports expose
the needed unit criterion. The `CharAndCard` import is needed and retained.

## Where the brief, the DAG or earlier work was wrong

The definition node has no numbered proof steps or declared proof dependencies.
The three remaining theorem docstrings describe substantial comparison results
between the derived ind-heart construction and geometric compact support, but
these comparisons are not given by the adjacent ambient-category interfaces.
Those interfaces give exact inverse image and open extension, adjunctions,
Grothendieck structures, and full faithfulness of the embedding; they do not
identify higher derived ind direct image with geometric proper direct image.

`Sheaf.Paper.CommonStageWeilShriek` supplies a geometric proper/open operation
and its recorded compact-support comparison, but imports this item. The import
cycle checker rejects using it here. Its existing comparison also does not
identify the derived ind-heart construction. No circular import, new comparison
axiom, or duplicate prime-unit theorem was introduced.

The first delivery dry run failed inside the launcher before preflight:
`sharedrepo.worktree` raised `subprocess.TimeoutExpired` because checkout of
`origin/sheaf-dag` exceeded its 600-second timeout. The required delivery tool was
retried without changing or bypassing the launcher scripts.
The retained retry log records a successful dry run (AUTO); its subsequent push
did not finish before that session ended. This session reruns the required dry
run and delivery against the current sources.

## Second reading by D8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
