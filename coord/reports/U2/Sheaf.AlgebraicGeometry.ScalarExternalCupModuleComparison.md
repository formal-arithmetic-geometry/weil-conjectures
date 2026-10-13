## What changed

The target proof now unfolds `externalCup`, applies a scalar cup/module cup comparison,
and rewrites both scalar pullbacks using a scalar/module cohomology pullback comparison.
Those two strictly smaller resolution comparison statements are isolated in new modules.

## Proved and sorry left

Proved `AlgebraicGeometry.Scheme.Modules.scalarExternalCup_moduleComparison`.
Added the strictly smaller sorry theorems
`scalarCup_moduleCup_compatibility` and
`scalar_moduleCohomologyPullback_comparison`, each with its own DAG node.

## No longer needed

None. All original imports remain required by the target statement or proof.

## Where the brief, the DAG or earlier work was wrong

The planned proof combines two substantial resolution comparisons without named
interfaces. The delivery splits those comparisons into independent intermediate nodes,
then combines them by a complete Lean proof.

## Earlier second reading (a previous round; superseded)

A second worker should check the unchanged target signature, the two strict reductions,
and that the theorem combines them after unfolding `externalCup`.

## New nodes

`lem-sc-scalar-external-cup-module-comparison`, `lem-sc-scalar-cup-module-cup-compatibility` and
`lem-sc-scalar-module-cohomology-pullback-comparison`, both under
`dag/nodes/sec-abelian-varieties/`. The change record is
`coord/changes/scalar-external-cup-module-comparison.md`.

## Second reading by U2

1. Compared the delivered declarations with the repository baseline; the target module was absent from this checkout, so no pre-existing signature could be altered. The split theorem signatures match their DAG `lean.statement` fields byte for byte.
2. Compiled all three modules with `lcompile.py --all`; compilation succeeds with no errors or warnings. The two unresolved declarations are named public theorems with complete source and proof sketches in docstrings, and have matching DAG nodes. No axioms, unsafe, opaque, extern, or hollow definitions occur.
3. Checked both split statements for edge cases and type alignment. They are strict intermediate comparisons used by the target proof, and are not restatements of the target. Searches recorded by the worker found no existing library or Mathlib declarations.
4. The target proof unfolds `externalCup`, applies scalar cup/module cup compatibility, then applies scalar/module pullback comparison twice. Imports are all used by statements or proof; no pruning was identified. The unit route through these two comparisons is retained.
5. DAG proof, proof dependencies, origins, Lean declarations, and report entries agree with the delivered code; the target theorem has no `sorry`, while the two split comparison theorems remain the explicitly documented open holes.

Changed only this second-reading report section; no Lean source, statements, or DAG nodes were modified.
