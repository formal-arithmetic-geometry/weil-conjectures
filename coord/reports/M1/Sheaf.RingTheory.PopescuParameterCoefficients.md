## What changed

Replaced the sorry in `Algebra.exists_popescu_parameter_coefficients` by a complete Lean
proof of the final coefficient calculation in Stacks 07FJ, item-done. Added
`Sheaf.RingTheory.PopescuParameterCoefficientModel` for the preceding parameter rescaling,
ideal bounds and raw Artinian model construction. The assigned theorem's signature and
visibility are unchanged. Its proof now imports only the new construction module; its
public imports are unchanged.

The new construction supplies constants u₀, coefficient constants, clearing units δ,
the map f₀ into D′, an evaluation map on D′[t], and injectivity of its restriction to
constants. It does not supply μ or the required coefficient equation in D′[t]. The Lean
proof contracts the original relation from Λ into D′ using that injectivity, divides by
δ^(2N), constructs μ explicitly as C(coeff * δ^(-2N)) * t^(2N), proves the polynomial
relation by distributing the finite sum, and proves evaluation compatibility by cancelling
unit powers. This is a reduction of the final algebraic step, not a complete proof of the
parameter construction and not a second name for the assigned theorem.

Both modules compile cleanly together using lcompile.py --all. Compilation used the
sandbox overlay; the construction module takes about 3 seconds and the assigned module
about 28 seconds. No new global definitions, changed interfaces, or forced adaptations.

## Proved and sorry left

Closed: `Algebra.exists_popescu_parameter_coefficients`, node
`lem-weil-pbc-popescu-parameter-coefficients` (the single original hole).

Added/left: `Algebra.exists_popescu_parameter_coefficient_model`, node
`lem-weil-pbc-popescu-parameter-coefficient-model`, in its own new module. Its proof is
exactly `:= by sorry`; the docstring supplies its source and complete proof in words.
No sorry remains in the assigned module, and no other hole is added.

This is a decomposition: one upper hole closed and one lower construction hole added;
net holes closed minus holes added is zero. The final coefficient calculation is proved.

## No longer needed

Removed the direct proof imports of `Sheaf.AlgebraicGeometry.Ogoma`,
`Sheaf.RingTheory.EssentiallySmoothBaseChange`, `Sheaf.RingTheory.EssentiallySmoothComp`,
`Sheaf.RingTheory.PopescuEnlargeSolutionModulo`, `Sheaf.RingTheory.PopescuSolutionModulo`,
`Sheaf.RingTheory.RegularLocalGeneratorsRegularSequence`,
`Sheaf.RingTheory.RegularRingSmoothAscent`,
`Sheaf.RingTheory.RegularSequencePolynomialVariables`, and
`Sheaf.RingTheory.RegularSequencePowers` from the assigned module. They are still needed
by the construction plan and remain its proof imports. None of their nodes or modules
is pruned from the targets' closure. No public import was removed or privatized.

All former proof dependencies are retained below the new model node. The assigned node's
proof_deps now names only the model node; its remaining arithmetic, scalar tower and
ring-homomorphism operations are elementary Lean proofs. Global pruning: none.

## Where the brief, the DAG or earlier work was wrong

The source file named by the node is absent in this machine's read-only literature tree.
Read the Stacks smoothing.tex source fetched into the item's scratchpad, including all
specified items and their justifications. The source writes n=N+dc while using e=8c in
its ideal bound. The existing assigned node already corrects that to n=N+d(8c); the new
construction retains that corrected exponent. The source's first displayed definition of
R uses t_1,...,t_m although subsequent steps consistently use t_1,...,t_d; the model uses
d polynomial variables, as does item-eighth-resolve. No statement correction was made.

The existing library declarations cover the component geometric and regular-sequence
results but do not state the simultaneous rescaling with its coefficient inclusions. The
new node isolates this part of the stated plan. Searches used LeanFinder, Loogle, grep
and LeanSearch through msearch.py; LeanSearch returned Internal Server Error and is
recorded as unavailable. No direct construction theorem was found. Blueprint searches
for "coefficient model" and "rescaled" found no matching blueprint node. The parent node
is not a realization of a unit statement or unit step; no unit route is bypassed.

Edge cases checked against the model argument: for d=0 take n=N>0 and an empty parameter
family; the maximal ideal is zero and the appended parameter is zero. The polynomial
coefficient proofs use finite sums without a nonemptiness assumption, so s=0 and d=0
require no exceptions. Empty singular generators force the contracted parameter power
to vanish; division by clearing units remains valid. The new statement requires units
rather than inverses of arbitrary elements. The Artinian coefficient carrier is in
Type(max u v), as in the original statement; its finite polynomial presentations and
localization transport are retained as an explicit remaining construction step.

## New nodes

`lem-weil-pbc-popescu-parameter-coefficient-model` states the rescaled-parameter and
injective Artinian coefficient model from 07FJ before item-done. It retains the source's
parameter construction, kernel equalities, ideal bounds and essentially smooth model,
and exposes their raw constant/evaluation data. The final polynomial coefficient
relation and μ are absent: they are constructed and proved in the assigned module.
Its own module is `Sheaf.RingTheory.PopescuParameterCoefficientModel`. The DAG proof
steps retain all former construction dependencies. The assigned node is updated to
match the compiled contraction, division, polynomial relation and evaluation proof.
No change record is needed: no existing signature or definition changed.

## Second reading by M1

1. PASS. Read the complete diff against the repository. The existing declaration
   signature is byte-for-byte identical; its visibility and public imports are
   unchanged. There are no definition changes or forced adaptations.
2. PASS. Read the proof from contraction through division, polynomial distribution
   and evaluation cancellation. Both modules compile locally without warnings.
   The only direct sorry is the named model theorem reported above; there are
   no definitions, forbidden declarations or hidden holes in the delivery.
   Explicit axiom checks are recorded below. Existential model data is eliminated
   only within a theorem proof; it does not define a global arbitrary witness.
3. PASS. Read Stacks smoothing.tex, the construction items and their justifications,
   and the existing solution-modulo and enlargement statements. The model is the
   preceding construction, with raw constants and evaluation data, and does not
   assert the final polynomial equation or supply its coefficients mu. The
   assigned proof supplies that strictly remaining algebraic step explicitly.
   Checked d=0 (zero maximal ideal, n=N, appended zero), s=0 (empty sums),
   and the cancellation requirement that delta is a unit. The positive N and c
   assumptions cover the exponent and kernel-power bounds. Independent searches
   used LeanFinder for Artinian local approximation and finite coefficient
   models, Loogle for MvPolynomial.eval₂Hom and Function.Injective (no hits),
   and grep/rg for Artinian, rescaling and solution_modulo. No direct model
   construction was found. Smooth descent hits do not give the local parameter
   rescalings or kernel conditions. The construction hole cannot be closed by
   a short application of the existing results.
4. PASS. The target is reduced directly to the construction and elementary ring
   operations; the nine former proof imports move to its construction plan.
   No proof-only import is public. All public imports remain required for the
   existing statement. The unit realized fields do not name this item or its
   new model, and the construction keeps the old route below that unit. No
   module is pruned from the targets closure. For explicit completeness, every
   old direct proof dependency replaced by the model is listed below; each is
   retained in the model proof plan rather than globally pruned.
5. PASS. Both Lean records agree with the actual signatures. The union of uses
   in each proof equals its proof_deps. The assigned node describes the actual
   contraction, unit division, explicit mu and evaluation steps; the model node
   carries the old construction dependencies, source, searches, creation and
   blueprint ancestry, and a complete natural-language construction proof.

Changes by the second reader: added this review and an explicit inventory of
replaced direct dependencies. No Lean proof, statement or node repair was needed.

Old direct proof dependencies retained below the model (no global pruning):

- `lem-weil-pbc-popescu-solution-modulo`
- `lem-weil-pbc-flat-local-hom-faithfully-flat`
- `lem-weil-pbc-faithfully-flat-ideal-contraction`
- `lem-weil-pbc-flat-height-formula`
- `lem-weil-pbc-field-regular-ring`
- `lem-weil-pbc-polynomial-ring-smooth`
- `lem-weil-pbc-regular-ring-smooth-ascent`
- `def-weil-regular-scheme`
- `lem-weil-pbc-localization-noetherian`
- `def-weil-pbc-localization-at-prime`
- `lem-weil-pbc-regular-local-generators-regular-sequence`
- `lem-weil-pbc-regular-sequence-polynomial-variables`
- `lem-weil-pbc-regular-sequence-powers`
- `lem-weil-pbc-ogoma`
- `def-weil-pbc-regular-sequence`
- `lem-weil-pbc-popescu-enlarge-solution-modulo`
- `lem-weil-pbc-essentially-smooth-composition`
- `def-weil-pbc-algebra-hom-quotient`
- `def-weil-pbc-essentially-smooth-ring-map`
- `lem-weil-pbc-essentially-smooth-base-change`
- `lem-weil-pbc-localization-base-change`
- `def-weil-pbc-finitely-presented-algebra`
- `def-weil-pbc-mv-polynomial-ring`

Explicit scratch-copy #print axioms checks: both declarations use exactly
`propext`, `Classical.choice`, `Quot.sound` and `sorryAx`. The remaining
`sorryAx` is expected for the open construction theorem; the upper theorem
is a decomposition, not an axiom-free completed target.
