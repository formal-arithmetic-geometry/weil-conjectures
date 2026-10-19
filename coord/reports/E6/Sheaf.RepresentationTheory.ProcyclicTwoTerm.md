## What changed

Proved `Rep.exists_procyclic_twoTerm_computation` with its original signature and all
three public imports unchanged. Updated its proof docstring to describe the direct
derived-invariants comparison actually implemented. The complex is the explicit functor
`Rep.actionTwoTerm`, constructed degree by degree.

Added six fully proved supporting modules: `ProcyclicComplex`, `ProcyclicInvariants`,
`ProcyclicDeltaFunctor`, `ProcyclicPrimitive`, `ProcyclicEffacement`, and
`ProcyclicTwoTermComparison`, under `Sheaf.RepresentationTheory`.
The two-term complex, invariant kernel, long exact sequence, periodic partial sums,
positive-degree effacement and universal-property comparison are all implemented in Lean.
The auxiliary fixed-generator lemma is private and proved. The primitive handles the
last residue explicitly; its proof also covers modulus one and zero coefficient modules.
No commutativity assumption on the ring was added.

The comparison uses the existing declarations for discrete-module abelianness,
coinduction, degree-zero continuous cochains and universality of right derived functors.
Existing holes in those imported dependencies remain their existing items. Choices of
coinduction objects and invariant functors occur inside theorem proofs, never inside a
new definition. Every new definition is an explicit construction.

Updated the item's proof, proof dependencies and proof origin to this route. Its
statement and lean attachment are unchanged. No existing definition, statement,
consumer or target is adapted. No change record or forced adaptation is needed.

Validation: the retained comparison initially exhausted the default heartbeat budget
while constructing the natural isomorphism between invariant realizations. Factored
that elementary naturality argument into a proved private helper with abstract functors;
the comparison then compiled remotely in 8.9 seconds at the unchanged default limits.
The retained diagnostic traces have been removed. The resumed delivery dry run compiled
all seven modules and passed preflight (dry-run commit `ecb0814d2f`). The axiom probe
for `ProcyclicEffacement` received no server answer; the tool explicitly allows the
merge to repeat that probe. The actual push repeats the delivery checks.

## Proved and sorry left

Closed the one original hole:
`Rep.exists_procyclic_twoTerm_computation` (`lem-exc-procyclic-two-term`).

Also proved `Rep.actionTwoTerm_isZero`, `Rep.actionTwoTerm_homology_zero`,
`Rep.actionTwoTerm_deltaFunctor`, `Rep.exists_procyclic_primitive`,
`Rep.actionTwoTerm_effaceable`, and `Rep.procyclic_twoTerm_cohomology_comparison`,
with their private proof helpers. `Rep.actionTwoTerm` and its terms, differential,
coefficient maps and term equivalences are explicit definitions.

Holes closed: 1. Holes added: 0. Holes left in the item and every added module: 0.
There is no decomposition into unproved intermediate results. This is a proof from
existing declared dependencies, not a claim that their transitive holes are closed.

## No longer needed

Removed these proof imports from the item module:

- `Sheaf.CategoryTheory.DiscreteModulesAbelian` (used in the supporting modules).
- `Mathlib.Algebra.Homology.HomologySequence`.
- `Mathlib.Algebra.Homology.HomologySequenceLemmas` (used by `ProcyclicDeltaFunctor`).
- `WeilConjectures.CategoryTheory.DeltaFunctor` (used by the supporting modules).
- `Sheaf.RepresentationTheory.CoinducedDiscreteEmbedding` (used by invariants and effacement).
- `Sheaf.Topology.ContinuousOpenNormalStabilizer` (used by the primitive).
- `WeilConjectures.CategoryTheory.EffaceableDeltaFunctorUniversal`, including its
  duplicate import (used once in the comparison).
- `Sheaf.RepresentationTheory.ContinuousCochainsDeltaFunctor`.
- `Sheaf.RepresentationTheory.CoinducedContinuousAcyclic`.
- `Sheaf.RepresentationTheory.ContinuousCochainsShortExact`.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`.

The interrupted candidate had also added
`Sheaf.CategoryTheory.EffaceableDeltaFunctorUniversal`; that unused import is removed.

The direct two-term proof no longer needs
`lem-exc-continuous-cochains-delta-functor`,
`lem-exc-coinduced-continuous-acyclic`, or
`lem-exc-continuous-cochains-short-exact` for a second delta-functor comparison,
and no longer needs `def-weil-abstract-derived-category` to localize an explicit
comparison chain map. The three obsolete cochain entries were removed from the item's
top-level `tool_uses`, preserving the order of remaining approvals.
The cohomology definition's preexisting import closure still uses the cochain results;
this report does not claim those modules are globally unreachable.

The original long-exact and naturality nodes remain used by the new delta-functor
node through Mathlib's `HomologySequence` API. The original abelian, coinduction,
open-normal-stabilizer and effaceability nodes remain used below the supporting nodes.
No unit statement or realized unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing node's nine-step plan unnecessarily compares with continuous cochains
and constructs an evaluation chain map before localizing. The unchanged Lean statement
asks for natural cohomology isomorphisms. Comparing the effaceable two-term
cohomology delta-functor directly with right derived invariants proves precisely that.
This is also the final identification stated in the current blueprint's third proof
paragraph. The main-20261015 source is under `sec-six-functors-basics`, whereas the
older node's source path remains under `sec-smooth-purity`; both proofs were read and
agree on the explicit effacement argument.

The earlier sandbox history recorded an interrupted candidate without complete records.
The retained work includes a repaired comparison elaboration timeout. This session
retained its seven modules and seven node records, checked their proofs and dependency
signatures against current sources, and updated the stale main theorem proof docstring.
No mathematical defect was found in the assigned statement. The private invariant-realization helper keeps the
chosen functor abstract during naturality checking; no definition or public signature
changed, and no heartbeat or wall-clock limit was raised.

## New nodes

`def-exc-action-two-term-complex`: explicit two-term action functor and its degreewise API,
realized by `ProcyclicComplex`.

`lem-exc-procyclic-homology-zero`: the invariant inclusion is the degree-zero kernel,
naturally in any specified realization of invariants, realized by `ProcyclicInvariants`.

`lem-exc-procyclic-delta-functor`: the two-term complex preserves short exact sequences
and its homology has connecting maps, realized by `ProcyclicDeltaFunctor`.

`lem-exc-procyclic-locally-constant-primitive`: finite periodic partial sums give a
locally constant translation primitive, realized by `ProcyclicPrimitive`.

`lem-exc-procyclic-two-term-effacement`: coinduction effaces each positive degree,
realized by `ProcyclicEffacement`.

`lem-exc-procyclic-two-term-comparison`: universality identifies the explicit two-term
homology with the recorded right derived invariants, realized by `ProcyclicTwoTermComparison`.

All six nodes have source passages, complete proof steps, dependency unions, three
kinds of recorded Mathlib search and verbatim Lean signatures. All are proved here;
none creates a new hole.

## Second reading by E6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
