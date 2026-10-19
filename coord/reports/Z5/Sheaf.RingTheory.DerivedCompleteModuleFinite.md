## What changed

Proved `ModuleCat.finite_and_completion_bijective_of_isDerivedComplete` in
`Sheaf.RingTheory.DerivedCompleteModuleFinite`, with its existing signature and all
public imports unchanged. Added private, fully proved sequence-algebra helpers.
For each ideal element, derived completeness makes the Roos endomorphism invertible;
applying degree-zero homology identifies it with the sequence difference map.
Bijectivity passes to ranges and to quotients by complete submodules. Cauchy geometric
sums establish the sequence condition for ordinarily complete modules. Induction on
finite ideal generators proves the sequence version of derived Nakayama.

Lift finite residue generators and take their finite span N. The existing finite-module
completion theorem makes N complete, so the quotient M/N has the sequence conditions.
Its reduction is zero; Nakayama gives M/N = 0. Thus M is finite, and the same existing
completion theorem proves bijectivity of its canonical completion map.

The proof uses `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence` and
`WeilConjectures.RingTheory.FiniteModuleComplete` directly, replacing their Sheaf
forwarding imports. Mathlib proof imports provide module products, exact products,
the degree-zero single/homology identification, and the required algebra tactics.
The item's existing node records the implemented six-step argument. No definitions
or statements visible to consumers changed, and no consumer adaptation is required.

## Proved and sorry left

Closed 1 of 1 original holes:
`ModuleCat.finite_and_completion_bijective_of_isDerivedComplete`
(node `lem-weil-derived-complete-module-finite`).

Added holes: 0. Remaining holes in the delivered module: 0. Split-offs: 0.
Every private helper is proved. The server single-file compile passed in 5.2 seconds;
`#print axioms` reported exactly `propext`, `Classical.choice`, and `Quot.sound`.
This is a proof without reliance on any remaining sorry in its dependencies.
The delivery dry run additionally checks all declarations of the delivered file.

## No longer needed

Removed proof imports:

- `Sheaf.CategoryTheory.Triangulated.DerivedLimitExistence`: replaced by its current
  upstream module `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`.
- `Sheaf.RingTheory.FiniteModuleComplete`: replaced by its current upstream module
  `WeilConjectures.RingTheory.FiniteModuleComplete`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`: its API is already public
  through the derived-limit existence module and the derived-completeness definition.
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`: the proof does not use
  its long exact sequence or cohomology detection criterion. The Roos triangle's zero
  first vertex immediately makes its second arrow invertible.

Pruned direct DAG proof dependencies and tool approvals:
`lem-sf-derived-homology-long-exact` and
`lem-weil-pbc-unbounded-derived-iso-cohomology`. Neither direction of a cohomology
vanishing equivalence is needed: only derived completeness implying invertibility of
the sequence difference is used. The general derived-limit existence and finite-module
completion nodes remain used. No claim is made that these pruned nodes are unused by
other parents elsewhere in the project.

The finite-free source and the converse sequence-to-derived-completeness implication
in the old proof plan are unnecessary. A finite submodule spanned by residue lifts is
complete by the existing finite-module completion theorem; its quotient suffices for
Nakayama. The unit record has no realized statement or proof steps to bypass.

Also removed redundant tentative proof imports
`Mathlib.RingTheory.Finiteness.Basic`, `Mathlib.LinearAlgebra.Quotient.Basic`, and
`Mathlib.CategoryTheory.Abelian.Exact`; their needed APIs are supplied transitively.
All existing public imports were retained.

## Where the brief, the DAG or earlier work was wrong

No statement defect was found. The DAG's full kernel/cokernel computation and converse
criterion were stronger than this proof needs. Its finite-free construction was a valid
plan, but using the finite span of residue generators gives a shorter implementation.
The node's proof, proof dependencies, proof origin, and pruned tool approvals now match
that route. Sources remain Stacks Tags 09BA, 09B9, 091R, and 091U, read in
`literature/stacks-project/more-algebra.tex`.

Edge cases are covered by the actual argument: the empty ideal generating set is the
base case of Nakayama; a zero residue module uses the empty finite span; zero modules
and the zero ring require no nontriviality hypothesis. The whole-ideal case is handled
by the same sequence argument. No arbitrary data is chosen from an unproved theorem.

The first resumed compile request returned no answer from the compile server; its
retry compiled successfully. No delivery had been attempted before resumption.

## Second reading by Z5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
