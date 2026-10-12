## What changed

Proved `AlgebraicGeometry.Proj.standardOpenProperties` in
`Sheaf.AlgebraicGeometry.ProjStandardOpenProperties`, with the public statement unchanged.
Six proved private helpers supply the positive-degree basis, arbitrary-family chart covering
criterion, homogeneous and ordinary localization units, homogeneous power factor, and finite
refinement. Only the original public Mathlib import remains.

The proof follows the existing seven-step plan. The chart covering criterion is proved first
and reused for the singleton unit criterion. Mathlib's ordinary localization unit criterion
packages denominator clearing, and `DirectSum.decompose` extracts the homogeneous factor.
The DAG proof records this ordering and the lemmas actually used. The item's node is not a
unit realization; the unit's statement and steps are unchanged.

Sources checked: Stacks [01M4](https://stacks.math.columbia.edu/tag/01M4) and
[00JP](https://stacks.math.columbia.edu/tag/00JP). The local literature files are absent,
so the published Stacks pages were read. Search ran through leanfinder, loogle and grep,
followed by direct inspection of the pinned Mathlib and source-library files.

## Proved and sorry left

Closed the sole original hole: `AlgebraicGeometry.Proj.standardOpenProperties`
(node `lem-weil-pbc-proj-standard-open-inclusion`). This is a complete proof from Mathlib,
not a decomposition through other sorry-bearing statements. No holes added or left.
All six private helpers are proved. Local compilation passes without warnings.

The proof handles zero rings and nilpotent elements without exclusions. Compactness permits
an empty finite subcover when the chart is empty. The covering criterion works for arbitrary
index types, including the empty type, before specialization to `Fin n`. The degree assertion
uses its stated nonzero-product hypothesis, and no stronger assumption.

## No longer needed

No original imports or DAG dependencies were removed: all five existing proof-dependency
nodes remain used through their Mathlib declarations. An experimental proof-only import of
`Mathlib.RingTheory.Localization.Away.Basic` was removed after compilation showed the
original import suffices. No additional Sheaf or WeilConjectures module is needed.

The explicit inverse construction and separate nilpotent/zero-ring branch in the old plan
are unnecessary; the chart unit criterion proves the unit assertions uniformly. The planned
`Sheaf.AlgebraicGeometry.ProjStandardOpenBasis` shortcut is unusable here because that module
imports this one; the basis is proved directly. No nodes or modules pruned.

## Where the brief, the DAG or earlier work was wrong

The public statement is correct and unchanged. The listed proof dependencies are Mathlib
leaves or definitions, rather than Sheaf modules to import. The source-library homogeneous
cover lemma is unnecessary because Mathlib's `affineOpenCover` supplies the same witnesses.
The route below the unit level was streamlined as described above; the node copy records it.

## Second reading by H3

1. **Public interface: pass.** Compared the sole delivered module with the repository
   using `diff -u`, and independently compared the complete text of the existing
   `standardOpenProperties` signature up to `:= by`: byte for byte identical.
   Imports, universes, namespace, existing docstring and module exposure are unchanged.
   The only new declarations are six proved private helpers; no definition changed,
   no change record is required, and no other Lean module is delivered.
2. **Proof and axioms: pass.** Compiled the whole sandbox with the prescribed
   `lcompile.py --all`: no errors or warnings. A scratch copy prints axioms for
   `positiveBasis`, `chartCover`, `chartUnit`, `ordinaryUnit`, `homogeneousFactor`,
   `finiteRefinement`, and `standardOpenProperties`: each uses exactly `propext`,
   `Classical.choice`, and `Quot.sound`, with no `sorryAx`. The delivered Lean has
   no `sorry`, forbidden declaration, hollow definition, or line over 100 characters.
3. **Split statements and edge cases: pass.** There are no split-off statements,
   new public statements, or new nodes. Read each private helper's proof: the chart
   cover criterion uses the actual opens range of `awayι`, so it needs no implicit
   surjectivity onto Proj. Its arbitrary index type includes an empty family.
   The singleton specialization correctly exchanges f and g. The ordinary-unit
   argument multiplies by the invertible denominator and uses k > 0. The factor
   argument uses `IsLocalization.algebraMap_isUnit_iff`, which already clears
   denominator torsion; e = n+d+1 ensures e > 0 and e*k >= d before projection.
   No cancellation or domain assumption is used. Zero rings and nilpotent g give
   empty charts and remain covered by these arguments. Nonzero a*f is used only
   for uniqueness of its degree. Compactness allows n = 0, including an empty
   cover of an empty chart.
4. **Route and pruning: pass.** Read the proof from its final conjunction downward,
   the five dependency records, Mathlib's Proj chart/basis declarations, localization
   unit criterion and graded projection formula. Re-searched via msearch grep with
   `positiveDegree|positive.*[Bb]asis|algebraMap_isUnit_iff|coe_decompose_mul_of_left_mem_of_le`,
   and searched both library roots for homogeneous bases, chart factors and this
   statement. The nearby `exists_factor_of_isUnit` factors ring maps, not homogeneous
   divisibility; `ProjStandardOpenBasis` imports this item and would create a cycle.
   No shorter existing result replacing the proof was found. The sole public import
   is needed by the statement itself. All five original proof dependencies are
   accounted for; nothing is omitted from `No longer needed`. Read the realized
   statement and seven steps of `dag/units/sk-thm-reduction.json`: this item is below
   those realizations, and none is bypassed or changed.
5. **DAG agreement: pass.** Compared the node files: only `proof` and `proof_origin`
   differ; the statement, Lean declaration record and dependencies are unchanged.
   The union of the seven steps' `uses` equals `proof_deps`. Steps 1–2 describe
   `positiveBasis` and intersections; step 3 is `chartCover` and `chartUnit`;
   step 4 is `ordinaryUnit` and `homogeneousFactor`; step 5 is the converse and
   degree assertion; step 6 is `finiteRefinement`; step 7 is the finite specialization
   of `chartCover`. The listed Mathlib leaves supply exactly those ingredients.

Changes made by the second reader: appended this independent review and recorded
one additional search. No Lean proof, signature, import, definition, or DAG repair
was needed. Closed holes remain 1, added holes 0, split off 0, pruned modules none.
