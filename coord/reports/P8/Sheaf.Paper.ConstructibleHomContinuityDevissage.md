## What changed

Proved `AlgebraicGeometry.ProEtale.constructibleHomContinuity_of_lisseGenerators` in
`Sheaf.Paper.ConstructibleHomContinuityDevissage` without changing any existing signature,
definition, visibility or import. Retained the previous formal devissage proof unchanged.

Applied the declared dependency `coefficientHeart_generation` to obtain its finite cone
witness. Strong induction on the witness index proves continuity of every entry.
For a generator, the canonical scheme-theoretic image factors its immersion into the
open map `a.toImage` followed by the closed map `a.imageι`. The supplied hypothesis
applies to exactly the composite functor in `coefficientHeartLocallyClosedExtension`.
Shift and isomorphism closure from the formal devissage theorem then give continuity
of the generator entry. For a cone entry, rotate its distinguished triangle and apply
extension closure to the earlier target and the shift of the earlier source. Shift
invariance removes the extra shift from the cone. The last witness entry equals the
specified constructible object.

Both field coefficient alternatives and the Noetherian hypotheses are unchanged.
The induction includes rank-zero generators, the zero complex and the empty scheme;
it assumes no boundedness of the diagram. No new statement or definition is needed.

## Proved and sorry left

Closed the only original hole:
`AlgebraicGeometry.ProEtale.constructibleHomContinuity_of_lisseGenerators`
(node `det-lem-constructible-ext-continuity-devissage`). Proved 1 of 1 sorries;
added 0 holes, split off 0. No `sorry` remains in the delivered module.
`constructibleHomContinuity_devissage` was already proved and is unchanged.

The proof uses the existing dependency
`AlgebraicGeometry.ProEtale.coefficientHeart_generation`
(node `det-cor-coefficient-heart-ii-generation`), whose own proof still contains
`sorry`. Its module is not changed. This is a complete proof of the specialization
from the declared generation theorem, with the induction and cone argument written
here, rather than a new copy or repackaging of the original obligation.

Remote single-file compilation passed without warnings (2.9 seconds). A separate
`#print axioms` check confirms the formal devissage theorem uses only `propext`,
`Classical.choice`, and `Quot.sound`; the specialization additionally reaches the
existing generation theorem's `sorry`.

## No longer needed

No original import, DAG dependency, node or module is pruned. The proof follows the
original DAG and its existing proof-only import `Sheaf.Paper.CoefficientHeartGeneration`.
Removed the earlier sandbox attempt's proof-only import
`Sheaf.Paper.ConstructibleExtContinuity`; neither `bounded_constructible_ext_generated`
nor its finite-extension interface is needed. That import was never in the assigned
repository module, so its removal does not claim a reduction of the targets' closure.

## Where the brief, the DAG or earlier work was wrong

The inherited report said `Sheaf.Paper.CoefficientHeartGeneration` was unavailable.
Its source and compiled module are now available, so the original DAG plan can be
implemented directly. Replaced the inherited alternative proof and restored the
unchanged current DAG node. No statement correction, definition repair, new node,
change record or forced adaptation is necessary.

## Second reading by P8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
