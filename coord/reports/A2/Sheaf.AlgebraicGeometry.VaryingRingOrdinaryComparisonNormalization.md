## What changed

Completed `AlgebraicGeometry.ProEtale.VaryingRing.ordinaryComparisonNormalization`
without changing its statement, its specified comparison isomorphisms, or any
shared definition. The only existing Lean module changed is the assigned item.
Added private proof imports of `VaryingRingOrdinaryModuleComposition`,
`VaryingRingOrdinaryOpenUnit`, and the adopted exact-single coherence library.
The public import of `VaryingRingOrdinaryEvaluationComparisons` stays unchanged.

The pullback equation follows from `ordinaryModuleEvalG_comp`. Private generic
lemmas prove the constant/degree-zero composition equation and composition of
pasted comparisons, including the realization equality transports. Keeping these
calculations over arbitrary categories avoids unfolding the scheme-site data.
A private predicate packages the component composition equation before
specialization. Two smaller proved lemmas handle pullback pasting and inversion
of the open comparisons; the mate-pasting step uses the existing square calculus
directly. These helpers retain exactly the specified equations.
The open equation uses the already proved `ordinaryOpen_mate`, Mathlib's mate
pasting and conjugation identities, and the pullback equation. Inverting the
resulting equality of inverse comparison isomorphisms gives the required forward
equation. The DAG proof and proof dependencies now record this argument.

All new helpers are private and proved. The argument applies at every index,
including zero, and to arbitrary commutative coefficient rings, including the
zero ring; it uses no nonzero, finite, flat, bounded, or cartesian hypothesis.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.ProEtale.VaryingRing.ordinaryComparisonNormalization`
(node `lem-sp-varying-ring-ordinary-comparison-normalization`).

The item has zero remaining sorries. No holes or new assumed statements were
added elsewhere. This is a proof from existing declarations, not a decomposition.

Validation: `lcompile.py` compiled the final assigned module with exit code zero
in 25.1 seconds, with no warnings. Its public theorem signature matches the
restored original verbatim. The delivery contains one existing Lean module and
its own DAG-node update; no consumer interface changed.

## No longer needed

No original import was removed, and no module is withdrawn.

The item's proof no longer needs the aggregate theorem dependencies
`lem-coef-semilinear-derived-sections`
(`Sheaf.Paper.SemilinearDerivedSections`) or
`lem-cbc-strict-tower-proper-open-calculus`
(`Sheaf.AlgebraicGeometry.StrictTowerProperOpenCalculus`).
Their broad calculus assertions are not used: exact-single coherence, the
ordinary module compositor equation, and the existing open-mate normalization
suffice. Their supporting definitions may remain transitively imported elsewhere;
this delivery claims no removal of those modules from the targets' import closure.
The ordinary-evaluation, ordinary-module-composition, and mate-pasting nodes stay.
`lem-sp-varying-ring-ordinary-open-unit` is now the explicit dependency for the
one-open normalization already proved in the library.

## Where the brief, the DAG or earlier work was wrong

The shared snapshot initially listed the module in the quarantine rework table,
but the current server queue restored it as a stage-3 proof item with one hole
and no item-specific build-error file. I used the restored module and preserved
its statement and Lean attachment.

The original plan's one-open normalization has already been proved separately as
`ordinaryOpen_mate`; repeating its localization and degree-zero recovery argument
is unnecessary. The new proof uses that theorem directly and preserves the unit
route. No mathematical statement error was found.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
