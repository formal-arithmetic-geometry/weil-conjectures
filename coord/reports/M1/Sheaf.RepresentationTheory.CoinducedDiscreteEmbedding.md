## What changed

Completed `Rep.exists_coinduced_discrete_embedding` in
`lean/Sheaf/RepresentationTheory/CoinducedDiscreteEmbedding.lean`, without changing
its signature, docstring, or imports. All constructions are local to its proof.

The endofunctor sends a module to locally constant functions with right translation,
and sends a morphism to pointwise postcomposition using `LocallyConstant.mapₗ`.
The stated theorem
`ProfiniteGrp.exists_openNormalSubgroup_right_invariant` supplies an open subgroup
inside each function stabilizer. The orbit function is locally constant on open
left cosets of the original stabilizer. Its linearity and equivariance give the
components of a natural transformation; evaluation at the identity proves
injectivity. Functor laws and naturality are proved by pointwise extensionality.
No witness is chosen from an unproved existence theorem.

Read Stacks Project `etale-cohomology.tex`, Definition 04JP and the final comparison
in Section 0DVG. Searches through leanfinder, loogle, msearch grep, and the local
library found the existing integer-coefficient construction in
`Sheaf.RepresentationTheory.LocallyConstantCochainsAcyclicEmbedding`. Its elementary
right-translation and orbit-map argument was adapted to general ring coefficients;
functoriality was supplied here. Mathlib supplies `LocallyConstant.comapₗ`,
`LocallyConstant.mapₗ`, and subgroup openness. The DAG's three proof steps and
unit route are unchanged, so no node edits are required.

Validation: the complete module compiles through `lcompile.py` with no errors or
warnings. The delivery dry run additionally compiles the module and probes its
axioms. Edge cases require no separate assumptions: for the trivial group the
orbit map evaluates to the identity, and for the zero module or zero ring the
same pointwise proofs apply. Finiteness of the coefficient ring is not used in
the construction; the existing statement is preserved.

## Proved and sorry left

Closed the only original hole:
`Rep.exists_coinduced_discrete_embedding`
(node `lem-exc-coinduced-discrete-embedding`). Proved 1 of 1 original sorries.
No sorries remain in the item. No holes were added and no statements were split off.

## No longer needed

None. All existing imports remain: the public imports supply the category and
locally constant module API, and the proof import
`Sheaf.Topology.ContinuousOpenNormalStabilizer` supplies the stated topological
lemma. The proof uses the discrete-action category underlying
`lem-exc-discrete-modules-abelian`, but does not need its abelian/enough-injectives
theorem. No modules or DAG proof steps are removed.

## Where the brief, the DAG or earlier work was wrong

No discrepancy. The planned right-translation action and left-coset argument
have the stated orientations, and the representation universe `max u w` admits
the function module without a universe change. No definition or statement repair
was necessary.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
