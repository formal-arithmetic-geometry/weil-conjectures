## What changed

Proved `Algebra.SubmersivePresentation.topologicalKrullDimAt_spec_eq` directly from the
already proved upstream `AlgebraicGeometry.topologicalKrullDimAt_eq_of_smoothOfRelativeDimension`.
Compute the presentation dimension, lift the field and algebra to a common universe by ring
isomorphisms, establish smooth relative dimension for the affine scheme, and transport the
local-dimension equality along the spectrum homeomorphism. Added a proved private helper
`dimAt_homeomorph_le` for this last elementary topological step.

The existing theorem signature and public imports are unchanged. Removed three unused
complete-intersection proof imports and added only proof imports
`Mathlib.Algebra.Field.ULift` and
`WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth`.

## Proved and sorry left

Closed the sole original hole:
`Algebra.SubmersivePresentation.topologicalKrullDimAt_spec_eq`
(node `lem-weil-pbc-standard-smooth-over-field-dimension-at-points`).
Added zero holes; no `sorry` remains in any delivered module. This is a proof, not a
decomposition. The second reader removed both proposed inequality holes and their new
modules/nodes:
`Algebra.topologicalKrullDimAt_spec_le_of_isStandardSmoothOfRelativeDimension` and
`Algebra.le_topologicalKrullDimAt_spec_of_isStandardSmoothOfRelativeDimension`.

## No longer needed

Removed direct proof imports:
- `Sheaf.RingTheory.CompleteIntersectionOverField`
- `Sheaf.RingTheory.LciConormalFreeRankCodimension`
- `Sheaf.RingTheory.SmoothLocalCompleteIntersection`

The following original proof-dependency nodes are no longer used by this proof:
- `lem-weil-pbc-standard-smooth-is-smooth`
- `def-weil-pbc-smooth-ring-map`
- `lem-weil-pbc-standard-smooth-conormal-basis`
- `lem-weil-pbc-smooth-over-field-local-complete-intersection`
- `def-weil-pbc-complete-intersection-over-field`
- `lem-weil-pbc-lci-conormal-free-rank-codimension`
- `def-weil-pbc-module-localization`
- `def-weil-pbc-localization-at-prime`

This is direct-import and proof-dependency pruning; no claim is made that these modules
leave the entire targets' import closure. Neither the rejected bridge nor the proposed
upper/lower-bound modules or nodes is delivered.

## Where the brief, the DAG or earlier work was wrong

The old search record described the upstream local-dimension theorem as resting on `sorry`.
Its current compiled axiom check shows only `propext`, `Classical.choice`, and `Quot.sound`.
It supplies a shorter proved route below the unit level. The worker's revised DAG still
referenced the rejected bridge, and the inequality docstrings were incomplete; removing
those unnecessary statements resolves both faults. The existing declaration's docstring
records the original mathematical proof plan; the DAG and this report record the actual
shorter Lean proof.

## Second reading by F1

1. Compared the delivered module with the repository using `diff`: the existing public
   theorem signature is byte-for-byte unchanged; no definition, public import, instance,
   attribute, or target statement changes. Only proofs, private proof helper, and proof
   imports change. No change record is needed.
2. Compiled locally with `lcompile.py`. The target and private helper have no holes or
   forbidden declarations. Scratch `#print axioms` checks show only the three allowed axioms.
3. Independently searched with leanfinder (open-neighbourhood dimension query), loogle
   (`Algebra.IsStandardSmoothOfRelativeDimension`), and `rg` across the current library and
   Mathlib. Found the closed upstream theorem and removed both split-off statements.
   Edge cases: the zero algebra has no prime Q; n=c gives dimension zero; independent
   field/algebra universes are retained by explicit ULift transport.
4. Read from the target down and used the shorter closed-library route. All unused proof
   imports are removed; the list above contains every removed original proof dependency.
   Read `dag/units/sk-thm-p1.json` `realized`: this subsidiary lemma and its complete-intersection
   route are not a realized unit statement or step, and all unit realizations remain unchanged.
5. Replaced the stale bridge proof/proof_deps/proof_origin with the route the Lean uses.
   Kept all other existing node fields unchanged. No new nodes or open statements remain.

Changed: replaced the inequality decomposition with a complete proof; removed two new
modules, two new nodes, the obsolete change record, and the linter suppression; corrected
DAG route, pruning list, and hole accounting.
