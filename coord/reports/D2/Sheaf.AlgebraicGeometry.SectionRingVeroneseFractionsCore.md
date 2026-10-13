## What changed

Second reading reconciled the stale sandbox with the repository: restored the
shorter `QuotientAddGroup.liftEquiv.bijective` argument in
`sectionRing_veronese_fraction_core`. Removed one redundant `simp only` line before the generator computation: the
following `change` already reduces the canonical quotient lift definitionally. The canonical map, theorem signature,
generator formula, and imports are unchanged. Updated the node's second proof step and
`proof_origin` to record D2's independent review, retaining the current node's
statement and review history.

## Proved and sorry left

Holes closed: none (0 of 0 direct holes in the repository module).
Holes added: none. Holes left: none. The existing theorem
`AlgebraicGeometry.Scheme.Modules.sectionRing_veronese_fraction_core` is already
proved; this delivery validates that proof rather than claiming new proof progress.
The canonical map is an explicit quotient lift, with no arbitrary existence witness.

## No longer needed

None: no imports, nodes, or modules were pruned. Both old proof dependencies
remain used: `lem-sc-section-ring-veronese-fraction-kernel` and
`def-sc-section-ring-veronese-fraction-map`. The latter supplies surjectivity,
explicit numerator data, and the cancellation computation.

## Where the brief, the DAG or earlier work was wrong

The assigned module already has a complete proof in the repository. The initial
sandbox report claimed the shorter lift-equivalence proof, but its Lean file still
contained separate injectivity and surjectivity arguments. Its node also carried
older review history. The second reader restored the current repository proof and
node history; no historical statement repair was undone.

## Second reading by D2

1. Compared the complete delivered module with the repository using `diff`.
   Verdict: the sole Lean difference is the removed redundant proof line; every
   declaration signature, definition body, docstring, and import is unchanged. No new change record is
   needed, and existing canonical-map and generator-formula repairs are preserved.
2. Compiled the original sandbox and the simplified module through `lcompile.py`.
   Examined the quotient construction and checked both declarations with
   `#print axioms` in a scratch copy. Verdict: no direct holes or prohibited
   commands; both declarations use exactly `propext`, `Classical.choice`, and `Quot.sound`. The canonical map descends a
   concrete direct-sum map; it chooses no witness of mere existence.
3. No statements or nodes were split off. Verdict: no added holes, no restatement
   under a new name, and no new statement requiring a duplication search. Read
   the kernel and numerator-map modules, including cancellation and surjectivity.
4. Read Mathlib's `liftEquiv` construction: its underlying map is definitionally
   the quotient lift, so its `bijective` property gives precisely the first
   conjunct. The second conjunct computes the quotient lift and cancels the
   tensor-power isomorphism. Verdict: the short route is already used; the two
   old proof dependencies are both needed and no unit step is bypassed. Checked
   `dag/units/sk-thm-curveestimate.json`: this helper is below the realized unit
   statement `thm-sc-proper-cohomology`, and the unit's route is unchanged.
   The public kernel import is necessary in the exposed canonical-map definition:
   changing it to a plain import produces unknown-identifier errors for the
   numerator map and kernel theorem. The compiler experiment was reverted.
5. Compared the node's Lean statement with the declaration and traced each
   proof step and dependency through the code. Verdict: statements, `proof`,
   and `proof_deps` agree; preserved all current non-owned node fields, noted the
   definitional reduction in the second proof step, and recorded this reading in
   `proof_origin`. The generic quotient argument uses
   no positive-degree or regularity assumption, so degree zero, exponent zero,
   zero and nilpotent denominators are included.

Changes made: reconciled the stale sandbox proof and node history with the current
repository, removed the redundant generator-reduction tactic, corrected the
progress accounting, and documented this second reading. The first dry run
rejected an unchanged Lean module; the final simplification supplies a concrete
proof change without claiming any newly closed hole.
