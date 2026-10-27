## What changed

Replaced the body of `WeilConjectures.clopen_completed_restriction_comparison`
by a composition of independently typed ordinary-restriction and completion
isomorphisms. Its signature is unchanged. The proof uses the existing
`IntegralOnSlice.canonicalCompletionUnitCriterion` on the actual ordinary
pullback, maps its specified unit through exact restriction, and composes with
the completion/restriction factorization. All three new imports of the item
are private proof imports. Remote `lcompile.py --all` compiled the three delivery
modules successfully in 51.6 s, 56.7 s and 58.1 s respectively, each below 60 s.

Added `Sheaf.Paper.OrdinaryIntegralNestedOpenRestriction` for the ordinary
uncompleted composition step, and `Sheaf.Paper.ClopenIntegralCompletionRestriction`
for the quotient-tower/Roos step before imposing completeness. These are separate
parts of the original argument: the first mentions no completion, and the second
mentions neither the arbitrary morphism f nor the second open A. Neither theorem
repackages the assigned conclusion or assumes its comparison as a hypothesis.

The main proof needs closedness only of U. The unused original closedness
hypothesis on A is retained verbatim. The two intermediate statements were
checked on A=U, U=V, empty A or U, identity f, zero complexes, and arbitrary
unbounded inputs: ordinary restriction still composes, and the zero-category
interpretation supplies the empty-open case. The completion factorization is
stated for all inputs, so completeness enters exactly through the existing unit
criterion in the main proof.

## Proved and sorry left

This delivery is a decomposition, not an independent proof of the two new
geometric comparisons. The item has one hole initially and zero holes after
the change. Closed the hole in
`WeilConjectures.clopen_completed_restriction_comparison`
(node `lem-fix-clopen-completed-restriction-comparison`). Its assembly proof is
complete from the two new named statements and the existing unit criterion.

Added two holes, with source and complete proof plans in their docstrings and
matching nodes:

- `WeilConjectures.ordinaryIntegralNestedOpenRestriction`
  (`lem-fix-ordinary-integral-nested-open-restriction`).
- `WeilConjectures.clopenIntegralCompletionRestriction`
  (`lem-fix-clopen-integral-completion-restriction`).

No other holes are added. Net hole change of the packet is +1. The assigned
comparison continues to depend on these two unfinished steps.

## No longer needed

No original public import is removed: the three public imports supply the
unchanged statement and definitions. The item adds only the two intermediate
modules and `Sheaf.Paper.QcqsCompletionUnitCriterion` as private proof imports.

The item's direct proof dependencies are now the two new nodes and
`lem-fix-qcqs-completion-unit-criterion`. The former direct dependencies
`lem-sf-clopen-coefficient-comparison`, `lem-sf-clopen-derived-compatibility`,
`lem-sfb-ringed-derived-monoidal-comparisons`,
`def-sf-ordinary-integral-derived-pullback`,
`def-pur-integral-derived-operations`, and
`def-pur-open-completed-restriction-data` are retained where needed by the
intermediate statements or their proof plans; they are not globally pruned.
In particular no module is withdrawn and no source-library declaration is removed.

There is no separate step transporting completeness to U or A in the assembly:
the canonical unit is inverted on V and then mapped through restriction. The
stronger all-input completion factorization supplies exactly the required
completed object. No Noetherian, finite-dimensional, constructible, affine or
prime-invertibility input is imported to obtain this comparison.

## Where the brief, the DAG or earlier work was wrong

The listed dependencies do not provide the two comparisons between the precise
functors in the assigned statement. `sf_clopen_derived_compatibility` provides
reduction, strict quotient-tower and completeness assertions for
`sfClopenDerivedRestriction`, not an identification of
`ordinaryIntegralDerivedPull` with the successive published
`OpenCompletedRestriction.derivedRestriction` functors, nor the required
completed-pullback factorization. The generic ringed-derived compositor needs
this identification of the concrete presentations before it can be used.

`OpenCompletedRestriction.open_completed_restriction` does include a factorization
field with the desired endpoints, but its existence theorem assumes invertibility
of ell in residue fields on both schemes. The assignment has no such assumption,
and clopenness does not imply it (take a scheme in characteristic ell). Likewise
`ordinaryCompletedIntegralPullback` requires Noetherian, dimension, invertibility
and constructibility assumptions unavailable here. These are interface gaps,
not counterexamples to the assigned statement. The new clopen factorization
isolates the genuinely needed assertion without adding those hypotheses.

The unit record `sk-rem-sf-pf-done` has no realized steps or statement declarations;
this decomposition does not bypass a realized unit route. The completion-unit
criterion is already in the same unit. The new nodes retain the original
generic ringed-derived comparison as a tool; the clopen Roos factorization also
uses the existing exact-product strict-limit and integral-operation localization
lemmas as tools, without replacing the unit's route.

## New nodes

`lem-fix-ordinary-integral-nested-open-restriction` records the ordinary uncompleted
compositor and exact open restriction identifications, in
`lean/Sheaf/Paper/OrdinaryIntegralNestedOpenRestriction.lean`. Its source is Stacks
03D8 and 06YY, the ordinary part of the assigned proof's step 3. It is independent
of any completeness hypothesis or completed pullback.

`lem-fix-clopen-integral-completion-restriction` records restriction of the strict
quotient-tower completion as completed integral pullback, in
`lean/Sheaf/Paper/ClopenIntegralCompletionRestriction.lean`. Its source is Stacks
08TC, 0941 and the restriction step of 09C3, the tower part of the assigned proof's
steps 1 and 2. It is independent of the second open and of the arbitrary map f.
Both nodes preserve the original chapter and unit. No change record is needed:
no existing signature, definition, attribute, visibility or shared module changes.

## Second reading by T8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
