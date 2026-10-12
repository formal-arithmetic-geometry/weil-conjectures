## What changed
The target module now reduces exactness to the tuple complexes of the sets of lifts over each
map `φ : W ⟶ U₀`, using `freeCechComplex_exact_iff_fibres` in the new proof-only import
`Sheaf.Paper.FreeCechComplexDecomposition`. It applies the existing
`Algebra.powerSetComplex_contractible`: its exactness clause for nonempty fibres and its
zero-complex clause for empty fibres. The target signature, existing definitions, existing
public imports, and existing docstring are unchanged. No change record is necessary.

## Proved and sorry left
`AlgebraicGeometry.freeCechComplex_exact` has a complete reduction proof and no local sorry.
It is not yet axiom-closed: it depends on the existing open power-set contractibility theorem
and the new comparison theorem. The only new sorry is
`AlgebraicGeometry.freeCechComplex_exact_iff_fibres`, in
`lean/Sheaf/Paper/FreeCechComplexDecomposition.lean`, with node
`lem-weil-pbc-free-cech-complex-fibre-comparison`. Its docstring gives the inverse basis
bijections, differential compatibility, and finite-support argument for the direct sum.
It proves a comparison, without asserting exactness of the tuple complexes.

## No longer needed
Removed the undelivered module `Sheaf.Paper.FreeCechComplexExactAux` and its two degree-case
nodes `lem-weil-pbc-free-cech-complex-exact-at-one` and
`lem-weil-pbc-free-cech-complex-exact-above-one`. Neither belongs to the repository.
The target's old direct proof dependencies `def-weil-pbc-etale-site` and
`def-weil-presheaf-modules-sheafification` now occur through the comparison node and remain
statement dependencies; neither node or module can be pruned from the library.
No old library module or public import is removed. `Sheaf.Paper.PowerSetComplexContractible`
is retained and actually applied. No entire existing node becomes unnecessary.

## Where the brief, the DAG or earlier work was wrong
Splitting the target into degree one and degrees above one merely partitioned the same
unresolved exactness problem. It supplied none of the basis comparison in the node's plan.
The two new node statements were copied from the full target and appended contradictory
“Strengthened form” text, so they did not match their Lean declarations. Their search
records were inherited rather than searches of those new statements. They are replaced by
one actual comparison step of the original argument, and fresh searches are recorded in
`searches.jsonl`. LeanSearch returned HTTP 500; LeanFinder, Loogle, and source grep ran.
The local read-only repository lacks the Stacks source file, so I read the obtained source
online: [03AT](https://stacks.math.columbia.edu/tag/03AT) and
[03F5](https://stacks.math.columbia.edu/tag/03F5). The comparison follows the decomposition
portion of those proofs; the target then uses the separately stated contraction.

## New nodes
`lem-weil-pbc-free-cech-complex-fibre-comparison` compares exactness of the evaluated free
Čech complex with range/kernel equality in each fibre's tuple complex. It is the change of
basis and block-diagonal comparison portion of the argument, not the original exactness
claim under another name. It does not use the contraction to establish the comparison.
Its statement uses the existing tuple differential, so its public import of the power-set
module is necessary; both imports added to the target are proof-only. No new definition,
axiom, or change record is introduced.

## Second reading by B2
1. Compared the delivered target with the repository using `diff`; its existing declaration
signature and docstring are byte-for-byte unchanged. No definition or target statement
changes. The replacement comparison is a new declaration in its own module.
2. Compiled both modules in import order with `lcompile.py`, without errors or warnings.
The target has no sorry; the comparison's named theorem has the sole new sorry. Checked
for prohibited declarations and hollow definitions: none. Scratch `#print axioms` checks
show only `propext`, `Classical.choice`, `Quot.sound`, and the expected `sorryAx`.
3. Checked the comparison against the decomposition in Stacks 03AT/03F5. Empty family:
all lift sets and all degree terms are zero. A singleton identity family: each lift set
is singleton and the differentials alternate zero and identity, including exactness at
degree one. Two identical members: each fibre is a two-point tuple complex. A map with
no lift contributes a zero block. A zero coefficient ring makes every module zero.
The finite-support preimage argument proves both directions, with no covering assumption.
Fresh LeanFinder, Loogle and grep searches and searches of Lean/upstream/DAG found no
existing comparison declaration; LeanSearch was unavailable. Related free-sheaf and
surjective-set Čech theorems require additional identifications and do not state this step.
4. Replaced the artificial degree split with the original basis-decomposition route and
an actual application of the existing power-set theorem. Checked `dag/units/sk-thm-p1.json`
`realized`; its statement and steps are preserved, and the required contractibility module
remains imported. No existing library node is pruned. Original public imports supply
signature constructions and their instances; new target imports are proof-only.
5. Updated the target's `proof`, `proof_deps`, and `proof_origin` to the reduction as written.
The new node has a self-contained statement, complete proof steps, matching verbatim Lean
signature, actual search records, provenance, creation metadata, chapter, and unit.
Changes made in this reading: replaced both degree-case sorries with one documented
fibre-comparison sorry, restored and applied power-set contractibility, corrected the DAG
and report, and removed the compiler's `haveI` style warnings.
