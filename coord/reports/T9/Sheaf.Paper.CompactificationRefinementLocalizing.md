## What changed

Proved `refinementLowerStarId_linear` using the existing uniquely normalized module
identity compositor and `refinementLowerStarId_naturality` by faithfulness of the
module forgetful functor. Proved `refinementOpenUnit_isIso` by showing the underived
extension-by-zero functor is fully faithful, transporting across the coefficient
isomorphism, and descending its invertible unit to the derived adjunction.

The open-unit argument follows the existing proof in
`Sheaf.Paper.CondensedOpenClosedRecollement` directly using public declarations.
Added the proof-only imports `Sheaf.Paper.ProfinitePointPullback` and `import all
Sheaf.SixFunctors.ProEtale.ModuleObject.BaseChangeTheorems.LowerShriek.ExchangeMono`.

Proved `refinementOpenRestriction_isIso`: the boundary equality gives the cartesian
open square. The existing proved `cartesianDerivedCounit` identifies the pullback
of extension by zero with an object on which the open counit is invertible, for
arbitrary unbounded complexes. A proved private categorical helper
`CategoryTheory.restrictionMate_isIso` conjugates the resulting invertible
left-adjoint comparison. Its component calculation proves that the conjugate is
the specified restriction map. The unit, naturality and triangle identities fix
its normalization. The categorical helper is proved for arbitrary categories;
it imposes no nonemptiness, boundedness, characteristic or finiteness condition.
The node's step 2 and proof origin record this realization.
All existing signatures, definitions and visibility are unchanged. Compilation through
the required `lcompile.py` service passed cleanly against the current published build
in 11.4 seconds on the current resumed run. The node explicitly records the
profinite-point, fully faithful open-extension, abelian base-change and recollement
dependencies of this route.
The standard delivery dry run checks compilation and preflight; the node update
requires independent review. The axiom audit confirms the dependencies reported below.

## Proved and sorry left

Closed 4 of the original 5 holes, all attached to
`det-sf-comp-coherence-refinement`:

- `AlgebraicGeometry.ProEtale.CondensedRing.refinementLowerStarId_linear`.
- `AlgebraicGeometry.ProEtale.CondensedRing.refinementLowerStarId_naturality`.
- `AlgebraicGeometry.ProEtale.CondensedRing.refinementOpenUnit_isIso`.
- `AlgebraicGeometry.ProEtale.CondensedRing.refinementOpenRestriction_isIso`.

One original hole remains, attached to the same node:

- `AlgebraicGeometry.ProEtale.CondensedRing.localizingRefinement_coherence`.

Added no holes and split off no statements. This is a partial proof delivery.
`#print axioms` for the two identity lemmas lists only `propext`,
`Classical.choice` and `Quot.sound`. The two open lemmas additionally depend on
existing admitted derived-category infrastructure (`sorryAx`); no new admitted
infrastructure was introduced.

## No longer needed

No planned node or module is pruned: the remaining original theorem proof
still requires its proper-base-change and localizing arguments.
All original dependency imports are retained. No modules are withdrawn.
The retained attempt's proof-only `import all
Sheaf.Paper.CondensedOpenClosedRecollement` is unnecessary and has been removed;
the needed unit argument is proved directly from its public ingredients.

## Where the brief, the DAG or earlier work was wrong

The retained attempt compiled, but its report did not mention that it had removed
five planned proof-dependency imports while leaving the corresponding obligations
open. Those imports are restored. Its use of a private recollement theorem is
replaced by a direct proof from public APIs. The fourth proof uses a different,
proved private theorem, `cartesianDerivedCounit`, via its module's proof-only
`import all`; its statement covers arbitrary unbounded complexes and has no
field, characteristic, properness or bounded-constructibility hypotheses.
No statement correction is needed.

## Second reading by T9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
