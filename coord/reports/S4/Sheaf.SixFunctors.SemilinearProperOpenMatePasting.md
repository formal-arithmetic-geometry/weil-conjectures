## What changed

Proved four existing declarations using the existing system model and Mathlib:
`betaInvApp_naturality`, `betaInv_isIso`, `openToS_isIso`, and `rhoOrdinary_exact`.
The two invertibility proofs transfer the essential-image and full-faithfulness
arguments from the already proved varying-ring constructions. They establish
invertibility of the specified maps, without choosing replacement comparisons.

Added proved private equalities identifying the three derived functors with the
varying-ring functors, using two generic equality-transport lemmas to keep proof
terms compact. Moved the existing open-unit theorem before its new use.
Kept `P`, `R`, and `J` as named definitions with unchanged bodies and explicit
functor types. Spelled `Derived` directly using the existing standard instance.
These definitionally equal presentation changes avoid eager localization
expansion. The four change records contain the old/new declarations and the
consumer checks. No theorem signature or public import changed.

Repaired the return of head `1d009cdc95`: the `Derived`, `P`, and `R`
change records now include all six missing archived consumer modules, with their
current unclaimed/quarantined status. The `J` record also retains the direct
archived system-functor consumer. The previous live-only downstream search was
incomplete because it omitted quarantine. No consumer source changes are needed;
the public theorem signatures are unchanged and the definition bodies are
definitionally equal. The retained module recompiles in 7.4 seconds in this repair.

Change records:

- `coord/changes/S4-semilinear-proper-open-derived-presentation.md`
- `coord/changes/S4-semilinear-proper-open-j-presentation.md`
- `coord/changes/S4-semilinear-proper-open-p-presentation.md`
- `coord/changes/S4-semilinear-proper-open-r-presentation.md`

The edited module compiled without source warnings through `lcompile.py`. After
factoring the equality proofs through generic transport lemmas, a diagnostic copy
including the standard delivery axiom probe compiled in 16.8 seconds. The probe
reported exactly the sixteen direct holes listed below and no forbidden axioms.

## Proved and sorry left

Closed 4 of the item's original 20 direct holes:

- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.betaInvApp_naturality`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.betaInv_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.openToS_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoOrdinary_exact`

Added 0 holes and split off 0 statements. The proofs use existing declarations
whose dependencies may still contain sorry; this is not a claim that the item's
complete axiom closure is finished. Sixteen original direct holes remain:

- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_adjunct`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.semilinearProperOpenMatePasting`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_identities`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoOrdinary_existsUnique`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoPushOrdinary_existsUnique`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoPullInv_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoR_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.rhoJInv_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_scalarRestriction`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.evalPushOrdinary_existsUnique`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.evalPullInv_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.evalR_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.evalJInv_isIso`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.gamma_evaluation`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.pi_components`
- `AlgebraicGeometry.ProEtale.SemilinearProperOpen.compositor_associativity`

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.VaryingRingProperOpenPasting`; the new foundational
proofs need `import all Sheaf.AlgebraicGeometry.VaryingRingProperOpenArrows`,
including its proved private derived counit and clopen-isomorphism helpers.
No node or module is withdrawn. In particular, the pasting module and the other
recorded dependencies remain part of the plans for the unfinished statements;
this packet does not claim their global pruning.

## Where the brief, the DAG or earlier work was wrong

The returned consumer inventory was correct: quarantine must be included even
when the live-only downstream query is empty. The earlier records' claim to have
found every consumer was incomplete and has been replaced by the archived user
tables. Some matches are conservative textual matches of unrelated short names;
none authorizes pruning or withdrawing the archived modules.

No disputed mathematical statement was found. The old reducible presentation
of the derived functors made the naturality proof expand localization data;
the definition presentation changes address that elaboration issue. The DAG's
first proof step now records the four realized foundational arguments. The
remaining proof steps and their dependencies are retained; the directly used
varying-ring arrows node is also recorded as a dependency.

## Second reading by S4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
