## What changed

Completed the DIFFERENT retirement of
Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology.
Preserved its complete original strict-henselization-model theorem as
AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_baseChange_globalHomology
in Sheaf.AlgebraicGeometry.StrictLocalSmallModel.BaseChangeGlobalHomology.
Its statement differs only in the declaration name, its proof body is byte-identical,
and its public and private imports are identical. Added a module-docstring explanation
of the distinction from the adopted canonical-localization theorem.

Withdrew the old module using deleted.txt. Updated both direct consumers,
StrictHenselizationCohomologyComparisonIso and StrictLocalBaseChangeModelGlobalHomology,
only in their private import and theorem reference, including one proof-docstring
reference. Updated only the existing node's Lean attachment. No new nodes, definitions,
axioms or statement corrections. Change record:
coord/changes/A3-retire-strict-local-global-homology.md.

The original source compiled with lcompile.py. The retained module and both adapted
consumers compiled together in sandbox import order (11.3, 10.8 and 18.2 seconds).
The proof uses the existing small-model continuity presentation and derived etale
cohomology continuity; colimit uniqueness identifies the invertible comparison with
the original mate. Source checked: Stacks 03Q9 and 0GIT, and the current blueprint's
strict-henselization-stalk-formula proof. No uniform torsion restriction is introduced;
all integer degrees and bounded-below objects remain covered.

## Proved and sorry left

Original item: zero textual holes. Closed: none (0 of 0). Added: none. Split off: none.
Retained theorem:
AlgebraicGeometry.Etale.smallModel_isIso_strictHenselization_baseChange_globalHomology,
node lem-weil-pbc-strict-local-base-change-global-homology, has a complete proof.
Both adapted modules also have zero textual holes. This is a zero-hole retirement
repair, not a claim of new proof progress or a decomposition.

## No longer needed

The ambiguous module
Sheaf.AlgebraicGeometry.StrictLocalBaseChangeGlobalHomology is withdrawn. Both
consumer private imports now point to the explicit small-model module. No mathematical
dependency is pruned: both existing proof dependencies and all three proof steps remain
needed and unchanged. The adopted WeilConjectures module and every adopted declaration
remain untouched. No public import is removed from the retained realization or its
consumers. No parent edge or unit step is removed.

## Where the brief, the DAG or earlier work was wrong

The generic proof brief describes a holed item, but the current item is a listed
DIFFERENT retirement with zero holes. The adopted theorem cannot replace it by a direct
application: its base scheme and structural map are different. The smallModel_ rename
preserves the precise original mate, matching the preceding retirement of the
small-model continuity presentation by G6. The retirement table lists three historical
consumers; current downstream and quarantine searches find only the two adapted here.
The historical third consumer, Sheaf.AlgebraicGeometry.StrictHenselizationStalkFormula,
is already an empty withdrawn module.
The existing node statement and proof remain correct.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
