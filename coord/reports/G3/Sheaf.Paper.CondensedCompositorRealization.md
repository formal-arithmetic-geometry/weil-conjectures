## What changed

Proved `WeilConjectures.CondensedCompositorRealization.refinementIso_exists` for its
unchanged arbitrary coefficient datum. Private proof helpers transport finite
etale origins through the actual reduction evaluation and prove invertibility of
the specified semilinear proper/open mate. The refinement proof then checks each
factor of the existing `systemRefinement` paste and packages `asIso` with its hom
unchanged. No public signatures, definitions, attributes or public imports change.

The proof imports `SystemProperOpenInvertibility`, `ProEtaleConstantModuleConstructibility`,
`ProEtaleFiniteModelLocalConstancy` and `ProEtaleFiniteModelStalks`. These reuse the proved
private helpers `scalar_origin`, `system_isIso_of_evaluations` and
`positive_stratification`, followed by the finite-model and finite-stalk lemmas.
The finite-field hypotheses on the public
`SystemProperOpenInvertibility` application theorem are absent from the generic
helpers used here. The semilinear interchange argument uses `gamma_evaluation`,
`StrictTower.gamma_isIso` and joint detection of isomorphisms. It never detects equality
of derived morphisms by their evaluations. Updated the item's node with this route;
the unsolved main theorem's existing plan is retained.

The final step uses a generic proved helper for `pasteRefinement`, so that the
concrete derived-category paste is handled through its invertible input component.
Private application lemmas separately check the reduction mate and the actual
`systemRefinement` component. Private object-evaluation and application lemmas normalize the exact integral
reduction before the final packaging lemma fixes its prescribed hom.

## Proved and sorry left

Closed 1 of the current item's 2 holes; added 0 holes; split off 0 statements.

Proved: `WeilConjectures.CondensedCompositorRealization.refinementIso_exists`.
The nine newly written private proof helpers are proved, with no holes.
This is a stage-3 proof from existing declarations, including the named
`SemilinearProperOpen.gamma_evaluation` dependency; it adds no replacement hole for that identity.

Validation: the cleaned file compiled through `lcompile.py` in 36.7 seconds without warnings.
The axiom check reports `propext`, `Classical.choice`, `Quot.sound` and `sorryAx`;
the existing admitted evaluation dependency remains to be proved. No new admitted
declaration is introduced by this delivery.

The sole remaining hole in the delivery is
`WeilConjectures.CondensedCompositorRealization.condensedCompositorRealization`,
under node `lem-pur-condensed-compositor-realization`. Its statement and `sorry`
body are unchanged. This partial delivery does not claim its composition square,
naturality or refinement coherence proved.

## No longer needed

No existing import, module or mathematical node is removed or declared obsolete.
The remaining main theorem still needs its coefficient-mate and reconstruction plan.
Binary CTF gluing and its local-model theorem are not needed for the origin witnesses;
finite constant models on a positive stratification give the required predicate directly.
For the auxiliary refinement isomorphism alone, comparison with a constant Z_l
restriction tower, completed refinement coefficient squares and reconstruction units
are unnecessary: finite quotient diagrams, their specified evaluation comparisons
and joint detection prove invertibility directly.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The existing strict-tower invertibility theorem needs
etale-origin witnesses, rather than only a constructibility assertion. The proof now
supplies those witnesses and transports them through the precise derived-evaluation
isomorphisms. Bounds come from the uniform constructibility clause; no extra
geometric field or Tor hypotheses are introduced. Identity refinements, zero objects
and empty schemes are included by the same origin construction and functorial paste.

The private origin construction and positive-stratification helper are generic tools
from nodes `lem-pur-system-proper-open-invertibility` and
`lem-weil-pbc-proetale-constant-module-constructibility`. The additional finite-model
and stalk tools are nodes `lem-weil-pbc-proetale-finite-model-local-constancy` and
`lem-weil-pbc-proetale-finite-model-stalks`. Their proof-level use is recorded in the
DAG, without modifying maintainer `tool_uses` approvals.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
