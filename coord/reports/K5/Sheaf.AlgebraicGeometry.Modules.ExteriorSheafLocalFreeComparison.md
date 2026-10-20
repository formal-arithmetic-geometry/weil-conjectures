## What changed

Completed the retirement item listed in coord/retire-items.tsv. Withdrew
Sheaf.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison, redirected its
node to the official WeilConjectures twin, and adapted all five direct importers.
The four consumer nodes that use the theorem now record the compatibility equalities
in their proof dependencies; the fifth needs no mathematical proof-dependency change.
Four callers now use the official theorem and rewrite its conclusions with the
proved equalities exteriorSheafPresheaf_eq_exteriorPower and
exteriorSheaf_eq_exteriorPower. The fifth, DeterminantSplitLinearBijective, only
needed its unused comparison import removed. Every caller signature and public
import is unchanged. No source-library file or target statement is edited.

Change record: coord/changes/retire-exterior-sheaf-local-free-comparison.md.
All seven retained modules compile individually through lcompile.py --all;
the longest took 23.5 seconds. The first dry run passed (CODEX). Its separate axiom
probes timed out for KoszulSelfExtStalkBases, DeterminantSplitChartComparison,
DeterminantSplitLinearBijective, and ExteriorSheafPresheafComparison; the driver
reported these as deferred to the merge check. The source-file compiles themselves
all passed, and no timeout limit was changed. The final delivery reruns the probes.

## Proved and sorry left

The item initially had zero holes. Holes closed: 0. Holes added: 0.
No sorry remains in the withdrawn item or either new module.

New proved declarations:
- AlgebraicGeometry.Scheme.Modules.exteriorSheafPresheaf_eq_exteriorPower
  (lem-sc-exterior-sheaf-presheaf-upstream-comparison).
- AlgebraicGeometry.Scheme.Modules.exteriorSheaf_eq_exteriorPower
  (lem-sc-exterior-sheaf-upstream-comparison).

The existing official exteriorSheaf_local_free_comparison is used unchanged.
This is a zero-hole retirement repair, not a claimed closure of a theorem hole.
All seven retained delivered modules contain zero sorry.

## No longer needed

Pruned module: Sheaf.AlgebraicGeometry.Modules.ExteriorSheafLocalFreeComparison.
All five direct private imports of it are removed. Its local Finsupp/free-section,
frame-coordinate, and local-unit helper implementations are supplied by the official
module instead. No upstream declaration is removed or replaced by sorry.
DeterminantSplitLinearBijective does not use the comparison theorem directly, so
its import is simply removed. The other four callers import the official module
and only the compatibility equalities they use.

No mathematical dependency nodes are pruned: the original coordinate and local
sheafification proof is retained upstream. The original node is reattached there.
Both new equality lemmas are used by consumers. The original ExteriorSheaf module
is still needed to preserve their public legacy types and is not retired here.

## Where the brief, the DAG or earlier work was wrong

The generic proving brief describes a holed theorem, but this assignment is a
retirement item with zero holes (coord/queue.tsv and coord/retire-items.tsv).
The old and official comparison statements differ because the exterior-power
implementations differ. Replacing the import alone would not preserve callers.
Uniqueness on pure wedges proves equality of those implementations, allowing a
complete retirement without changing definitions or weakening statements.
No unit-route step is bypassed, and no further proof obligation is split off.

## New nodes

lem-sc-exterior-sheaf-presheaf-upstream-comparison records equality of the two
sectionwise exterior-power presheaves, proved using the legacy uniqueness theorem
and the upstream pure-wedge restriction formula.

lem-sc-exterior-sheaf-upstream-comparison records equality of the two sheafifications,
proved by applying the same sheafification functor to the presheaf equality.

Both follow the determinant/exterior construction in the Riemann--Roch blueprint
paragraph, with the implementation comparison explicitly marked as an agent proof.
Mathlib searches used LeanSearch, Loogle, LeanFinder, and grep, and direct searches
of both library roots found no existing compatibility theorem. The statements
assume no freeness or nonzero-ring hypotheses and include all edge degrees.

## Second reading by K5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
