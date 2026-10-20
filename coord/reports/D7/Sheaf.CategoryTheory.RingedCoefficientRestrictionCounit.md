## What changed

Completed the proof of `CategoryTheory.RingedCoefficientCounit.ringedCoefficientRestrictionCounit`.
The theorem signature and visibility are unchanged. The proof establishes the ordinary and complex transpose identities, the localized kappa equation,
the representative derived transpose, counit compatibility on K-injectives, and transport to every
derived object. Two strictly separate construction results required by the target route are stated
in new modules and imported by the item.

## Proved and sorry left

Closed one original sorry in
`CategoryTheory.RingedCoefficientCounit.ringedCoefficientRestrictionCounit`.
Two strictly separate construction results remain as named split theorems (net decomposition:
one hole closed and two holes added):

- `CategoryTheory.RingedCoefficientCounit.exists_derivedPresentation` in
  `lean/Sheaf/CategoryTheory/RingedCoefficientRestrictionDerivedPresentation.lean`.
- `CategoryTheory.RingedCoefficientCounit.coefficientChange_exists` in
  `lean/Sheaf/CategoryTheory/RingedCoefficientRestrictionCoefficientChange.lean`.

The item module contains zero remaining holes. The split holes have nodes
`lem-pur-ringed-coefficient-derived-presentation-exists` and
`lem-pur-ringed-coefficient-change-normalization`, respectively.

No other sorries were added. Each split statement has a matching DAG node and a complete proof
plan in its docstring.

## No longer needed

The retained proof no longer imports these modules directly:

- `Sheaf.CategoryTheory.ModulePullbackPushforwardAdjunction`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.CategoryTheory.RingedToposDerivedPushforwardComposition`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.Paper.ProEtaleProjectionFormulaArrows`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.Paper.RingedTopoiDerivedPullback`

The module-adjunction, derived-adjunction, derived-pushforward-composition, coefficient-adjunction
and derived-pullback declarations remain cited by the two split proof plans. The projection-formula
arrows and canonical tensor-pullback modules are unnecessary: the presentation's Hom formulas and
ordinary scalar-unit fields already supply their role. Thus nodes
`def-weil-pbc-projection-formula-arrows` and
`lem-weil-pbc-ringed-topoi-derived-tensor-pullback` are not used by the proof. All obsolete
parent `tool_uses` entries are removed except `lem-pc-kflat-resolution`. This is pruning of the
parent proof route, not a claim that all seven modules leave the targets' global closure.

## Where the brief, the DAG or earlier work was wrong

The earlier packet report incorrectly said the item theorem itself remained open; the theorem is
now proved. The construction and coefficient-coherence steps are independent results with their own
interfaces, so they are retained as named declarations rather than hidden inside the item proof.
The generic derived-adjunction scratch helper has also been completed and compiled; it does not
supply the normalized ringed coefficient comparisons and is not added to the delivery.

The initial/resumed reference timestamps observed in `.budget` were 1792425722 and
1792437746.8674452, respectively (attempts recorded in `dry-run-resume.log` and
`dry-run-final.log`). The dispatcher reset the reference clock between resumed attempts.
No worker edit to the budget or launcher was made.

Validation: all three sandbox modules compiled with no warnings; the final full compile took
4.5 seconds, 0.1 seconds and 38.8 seconds. Preflight subsequently requested a change record
for the top-level elaboration options; it is provided below.

## New nodes

Added the nodes `lem-pur-ringed-coefficient-derived-presentation-exists` and
`lem-pur-ringed-coefficient-change-normalization`, together with their modules
`lean/Sheaf/CategoryTheory/RingedCoefficientRestrictionDerivedPresentation.lean` and
`lean/Sheaf/CategoryTheory/RingedCoefficientRestrictionCoefficientChange.lean`.

Change record: `coord/changes/ringed-coefficient-counit-elaboration.md`.

A later dry-run compile exceeded 60 seconds. Profiling the unchanged proof completed in
19.7 seconds: no individual declaration elaboration or kernel check exceeded 3 seconds;
the largest reported command was the standard private-module linter (7.4 seconds).
The diagnostic profiler options were then removed. No limit was changed and no proof was
split to avoid this timeout.

Performance repair: restricted the representative theorem's broad transparency override to
the two tactic steps that require the termwise-composition definitional equality. The rest
of that proof now respects transparency. The resulting module compiled without warnings
in 26.5 seconds. This is a proof-only elaboration change, with no mathematical interface edit.

Final performance repair: the ordinary complex transpose now rewrites both ordinary Hom
equivalences explicitly by `homEquiv_unit`, with the conversion override scoped to that rewrite.
This avoids the previous expensive implicit conversion through the adjunction implementation.
The module compiled in 16.4 seconds; the final full sandbox compile succeeded without warnings:
coefficient change 3.7 seconds, presentation existence 3.4 seconds, item 21.1 seconds.

On the latest resumed attempt the dispatcher reset `.budget.start` again to
1792453655.0053704; `dry-run-worktree-retry.log` reported the new 35-minute reference.
Useful proof work continued: `scratchpad/RestrictionLift.lean` now proves the complete
normalized coefficient-restriction component, including restriction exactness, the ordinary
composition isomorphisms with identity underlying maps, localization and its factorization
equations. It compiles (53.6 seconds); the two remaining warnings concern unused section
variables and the scratch module's private-only declarations. This scratch work is not part
of the delivery and introduces no additional hole or public interface. The remaining direct-image
and coefficient coherence parts still require the separate results in the two split nodes.

## Second reading by D7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
