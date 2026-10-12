## What changed
The original theorem `HomologicalComplex₂.verticalCutoff_column_quasiIso_strict`
keeps its complete signature and is proved by splitting on `a ≤ 0`.
The new module `Sheaf.Algebra.Homology.VerticalCutoffColumnQuasiIsoStrictCases`
proves the nonpositive case directly: the lower cutoff is zero, the cokernel
projection is an isomorphism, and the specified truncation map is an isomorphism.
The new module `Sheaf.Algebra.Homology.VerticalCutoffColumnQuasiIsoStrictPositive`
states the remaining positive case with its complete contractible-kernel proof
in words. Both case imports in the core are private proof imports.
No existing statement, definition, declaration visibility, or target is changed.

## Proved and sorry left
Closed the original hole
`HomologicalComplex₂.verticalCutoff_column_quasiIso_strict`
(node `lem-sp-vertical-cutoff-column-quasiiso-strict`) by reduction to endpoint cases.
Also fully proved the new declaration
`HomologicalComplex₂.verticalCutoff_column_quasiIso_strict_nonpositive`
(node `lem-sp-vertical-cutoff-column-quasiiso-strict-nonpositive`), with only
`propext`, `Classical.choice`, and `Quot.sound` in its axiom printout.
The sole added hole is
`HomologicalComplex₂.verticalCutoff_column_quasiIso_strict_positive`
(node `lem-sp-vertical-cutoff-column-quasiiso-strict-positive`).
The core therefore still uses `sorryAx` through this explicit smaller positive case.
This is a decomposition, not a complete proof of the original theorem: one original
hole closed and one new hole left, net zero holes in the affected import closure.
There is no sorry in any definition and no arbitrary data chosen from an open theorem.

## No longer needed
Removed the redundant direct import of
`Sheaf.Algebra.Homology.DoubleComplexVerticalWindow` from the core and from both
new endpoint modules: `DoubleComplexVerticalTowerMaps` already publicly imports it.
No module is pruned from the target import closure.
Neither old proof dependency (`def-sp-double-complex-vertical-window` and
`lem-sp-double-complex-vertical-tower-maps`) is obsolete: both supply the notions
used in the signatures and endpoint calculations. The core now uses them through
the endpoint modules and records the endpoint nodes as its direct proof dependencies.

## Where the brief, the DAG or earlier work was wrong
The submitted core DAG proof step cited its own node, while its `proof_deps`
listed the endpoint nodes. Replaced the self-reference by two elementary steps
whose cited nodes agree with the actual Lean applications.
The first submission added two holes and closed only the upper one; the second
reading closed the nonpositive case, reducing the added holes to one.
The new endpoint docstrings initially only gestured at the argument, and their
nodes copied irrelevant cases and inherited review records from the parent.
The docstrings and plans now describe their own cases; spurious inherited review
records were removed. The new nonpositive theorem's unused hypothesis binder names
are prefixed with underscores; no existing signature is affected.

## New nodes
- `lem-sp-vertical-cutoff-column-quasiiso-strict-nonpositive`, proved in
  `Sheaf.Algebra.Homology.VerticalCutoffColumnQuasiIsoStrictCases`.
- `lem-sp-vertical-cutoff-column-quasiiso-strict-positive`, the sole remaining hole in
  `Sheaf.Algebra.Homology.VerticalCutoffColumnQuasiIsoStrictPositive`.

## Second reading by G2
1. Compared the core module with the repository using `diff` and the declaration
   signature parser: the only existing theorem signature is byte-for-byte unchanged;
   only its proof and imports change. The other two modules and nodes are new.
   No existing definition or public visibility changes. Verdict: pass.
2. Compiled all three modules in import order with the prescribed `lcompile.py`.
   Independently compiled scratch copies with `#print axioms` for every theorem.
   The nonpositive theorem has exactly the three allowed foundational axioms;
   the positive theorem and core additionally have only the explicitly accounted
   `sorryAx`. Inspected the source: exactly one named theorem has `sorry`; no axiom,
   unsafe, opaque, implemented_by, extern, or data definition occurs. Verdict:
   valid partial reduction, not an axiom-free completion of the original theorem.
3. Read Stacks tag 0118, Section 12.15, canonical cochain truncations (3) and (4),
   and the local Mathlib truncation and complementary-embedding APIs. The endpoint
   signatures retain L, g, hg, q and hq; the sign assumption specializes only a.
   Tested the reasoning on a = 0, negative a, b ≤ 0, L = 0, a = 1, b = a + 1,
   b ≥ a + 2, and zero/nonzero differentials. In the positive case a - 1 and a
   are both nonnegative; the adjacent-endpoint map is cycles to homology, while
   the other case is terms to opcycles. Its kernel is the same two-term image
   complex. The new holes have been reduced to this genuine remaining case after
   the other case was proved. Repeated searches with different terms via
   `msearch.py` LeanFinder (zero-cokernel projection), Loogle
   (`shortComplexTruncLEX₃ToTruncGE`) and grep (cokernel/truncLE/truncGE), plus `rg`
   over `lean/Sheaf` and `lean/WeilConjectures`. Mathlib supplies a single-cutoff
   cokernel-to-truncGE quasi-isomorphism, not the required nested-cutoff comparison
   with the specified hq; no duplicate full comparison found. Verdict: true,
   strictly restricted remaining case, fully documented; no mere renamed item.
4. Used the shortest route for the nonpositive case (isomorphisms, without a
   contractible-kernel construction), removed redundant window imports, and kept
   proof-only endpoint imports private. No target-reachable module is pruned.
   Read `dag/units/sk-prop-av-pqf-finite.json`: its `realized` statement and sole
   step are empty, so this node realizes no fixed unit step that the case reduction
   could bypass. Verdict: route preserved, pruning report complete.
5. Checked all three node records against their theorem signatures and plans.
   Fixed the core self-citation; `proof_deps` now equals the union of `proof.uses`
   on every delivered node. The new records carry source, searches, blueprint
   origin, chapter/unit, creation data and verbatim Lean statements. Removed copied
   parent review attestations from the two new nodes. Verdict: consistent.

Changes made during this reading: proved the nonpositive endpoint theorem;
removed redundant imports; completed both endpoint docstrings and node plans;
repaired the core DAG dependency steps; removed spurious new-node review metadata;
rewrote this report to account honestly for the remaining hole and net-zero reduction.
