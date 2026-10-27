## What changed

Proved `AlgebraicGeometry.Scheme.pbcActualCompletedPullback_tower` in
`Sheaf.Paper.PbcActualStrictPullback`, with its signature, definitions and public
imports unchanged. Added proof-only imports of all of
`PbcCompletedPullbackActual` and `CompletedTowerPullback` to reuse their proved
private comparison lemmas, and of `StratumCompletionUnitRestriction` for its
normalized strict reduction comparison.

The proof implements the last step of `def-weil-pbc-completed-pullback`:
conjugate `stratumReductionIso` by the normalized ordinary/tower presentation
transports, apply the specified derived limit, and compose with the inverse of
`actualCompletion_quotient`. The augmentation transport equation and the
constant/limit unit identification prove the exact required unit equation.
These are natural isomorphisms on the ambient category, whose restriction gives
the required existence assertion. For uniqueness, cancel the constructed
inverse and use injectivity of the reflector's Hom bijection into its complete
output. No input-completeness assumption beyond the original statement is
introduced, and the argument applies to the empty scheme and zero object.

This uses the existing proved parts of the planned argument, rather than
repeating the K-flat representative and Koszul comparison constructions inside
`completedPullback_isCompletion`. The node's existing strict comparison,
augmentation and intrinsic-reflection route is retained; its attachment is not
changed (the definition node currently attaches the Qbar interface).

Read Stacks `proetale.tex`, `lemma-pushforward-Noetherian-case`, clauses (2),(5)
and its proof, the item and dependency declarations, and the unit realization
record. Search via msearch LeanFinder for uniqueness of unit-compatible
reflection comparisons returned generic reflector lemmas; Loogle returned
`Adjunction.leftAdjointUniq`. Local searches located the already proved strict
transports and the quotient/actual-reflector comparison, so no additional
mathematical statement was needed.

Validation: lcompile.py compiled the final module cleanly in 11.5 seconds.
The import-direction check allows the explicit stratum-comparison import.

## Proved and sorry left

Closed the one existing hole:
`AlgebraicGeometry.Scheme.pbcActualCompletedPullback_tower`
(blueprint `def-weil-pbc-completed-pullback`).

Proved 1 of 1 sorries in the item. Zero sorries remain in this module; zero
holes were added, and zero statements were split off. Dependencies retain their
existing status; this report does not claim that their transitive axioms have
all been eliminated.

## No longer needed

None. No import was removed, and no node or module is withdrawn or claimed as
pruned. The proof reuses the existing strict-tower and reflector comparison
infrastructure, including its original mathematical dependencies. The separate
objectwise wrapper `completedPullback_isCompletion` is not called, because its
proved natural comparison constituents give the required natural isomorphism
directly; its module remains needed and imported.

## Where the brief, the DAG or earlier work was wrong

No mathematical correction was required. There is no definition repair,
statement change, new node or change to the unit route. The item module has no
separate primary `lean.module` attachment: its docstrings correctly identify
`def-weil-pbc-completed-pullback`, whose attachment currently names the Qbar
completed-pullback module. Its existing last proof step covers the proof here.

## Second reading by G3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
