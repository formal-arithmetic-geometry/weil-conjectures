## What changed

Recovered the proof packet from the returned J1 landing recorded in
coord/repair-notes/Sheaf.Paper.CompletedTowerPullback.json, without running git
in the shared repository. Proved all three original holes in
Sheaf.Paper.CompletedTowerPullback with the existing exact-derived API,
restriction/pullback coefficient square, strict reduction comparison and
unit-compatible Koszul/quotient comparison. The constant comparison is
uniquely determined by its actual universal counits; the completion comparison
is built from a single strict tower isomorphism and preserves the specified unit.

CompletedReductionUnit relocates the six existing augmentation declarations;
CompletedPullbackInterface relocates fourteen existing exact constant/pullback
interface declarations. Signatures and construction bodies are preserved and
re-exported by the original modules. Four comparison modules replace their
public CompletedTowerPullback import with CompletedReductionUnit. The stratum
comparison replaces its public CompletedPullback import with the earlier
CompletedPullbackInterface. These changes remove source import cycles rather
than changing coefficient data or choosing unnormalized comparison maps.

The two current-base definition nodes record these fully proved constructions.
The completed-pullback proof steps and dependencies now describe the Lean proof.
The stratum node spells out its existing completion-unit construction so its
dependencies point to the earlier interfaces. Its mathematical hypotheses,
conclusions and every Lean signature stay unchanged. Current-base review metadata
is preserved; historical review results from the returned patch are not claimed
as reviews of this repaired packet.

All nine packet modules compiled without warnings through lcompile.py --all
on this repair retry; the item took 50.2 seconds under the unchanged 60-second
limit. Earlier retained compatibility checks compiled the consumers below. Both modules
named by the global-build return were compiled unchanged against that packet:
CompletedPullbackReduction in 39.8 seconds and CompletedTowerDirectImage in
35.5 seconds. Neither consumer is delivered because neither needs adaptation
on the current base. No source-library file or target statement is changed.

Repair of returned head 3303661f6cd: added the four missing consumers to the
change record's Users table after checking their current source uses and claims.
ConstructibleCompleteBaseChange uses towerPull; ExchangeFunctoriality,
FiniteExtensionCompactSupportBaseChange and FiniteExtensionProperBaseChange use
TowerComplete. Their types and meaning are unchanged because relocation preserves
the declaration bodies and public re-exports. No consumer source edit is needed.
The delivery tool fetches current sheaf-dag and builds the rebased commit itself.

Change record: coord/changes/A4-completed-tower-pullback-interface.md.
The fresh scan of twenty relocated names found 110 textual consumer modules;
all are covered in its Users table, with current claim holders. This inventory
also includes textual final-name matches in other namespaces; it does not assert
that those unrelated declarations use the relocated interface.

## Proved and sorry left

Closed 3 original holes, all under def-weil-pbc-completed-pullback:

- AlgebraicGeometry.Scheme.completedPullbackConstantIso_exists.
- AlgebraicGeometry.Scheme.completedPullback_reductionEvaluation.
- AlgebraicGeometry.Scheme.completedPullback_isCompletion.

Remaining holes in the item: zero. Added holes: zero. Split-off holes: zero.
The two new modules contain zero holes; they relocate existing proved data
and statements and are not decompositions of any of the three holes.

The import-only adaptation of StratumCompletionUnitRestriction retains its
11 existing named theorem holes, all belonging to
lem-weil-pbc-stratum-completion-unit-restriction:
stratumModuleReductionIso_exists, stratumReductionIso_exists,
stratumFiniteCoefficient_naturality, stratumReduction_normalization,
stratumReduction_evaluation, stratumReduction_augmentation,
stratumRestriction_limits, stratumRlimComparison_isIso,
stratumCompletionComparison_unit, stratumIntrinsicComplete_preserved,
and stratum_completion_unit_restriction. None is added or changed.
All other delivered modules have zero holes.

## No longer needed

The direct public import of Sheaf.Paper.CompletedTowerPullback is removed
from CompletedConstantCoefficientEquivalence, CompletedConstantPresentationTransport,
CompletedKoszulQuotientComparison and CompletedQuotientUnitNormalization; each
needs only the earlier normalized reduction augmentation. The direct public
import of Sheaf.Paper.CompletedPullback is removed from
StratumCompletionUnitRestriction; its exact interface is enough.

No node or module is withdrawn or globally claimed pruned. The existing exact
route already avoids a general diagram K-flat replacement construction for
pullback. The completed-pullback node also owns other declarations, so its
other needed proof dependencies remain. The unit route is preserved.

## Where the brief, the DAG or earlier work was wrong

The item has no direct lean.module attachment: its declarations share the
completed-pullback node, whose current primary attachment is PbcQbarCompletedPullback.
The three actual holes were found from their docstring blueprint tags.

The shared repair note records historical failures of two consumers and several
returned suspects from the same batch. Both current original consumers compile
against the restored packet. Removing the historical redundant rfl from the
current reduction consumer is incorrect: its preceding simp leaves a definitional
projection equality that rfl closes. The final delivery retains both originals.

The previous coarse imports put earlier exact and augmentation data behind the
later completed-pullback proof, creating source cycles when that proof uses the
published comparison theorems. Relocating the earlier data preserves its
mathematical definitions and fixes the layering. The change record keeps the
full relocation inventory and the return evidence.

## New nodes

- def-weil-pbc-reduction-augmentation: the already proved unique strict quotient
  unit and its uniquely normalized derived augmentation, in CompletedReductionUnit.
  Source: Stacks 06YS, 06YY, 099N and the existing construction. The retained
  Mathlib searches identify the generic derived-lift API; the normalized quotient
  construction is project-specific. No new proof obligation is introduced.
- def-weil-pbc-exact-pullback-interface: the existing exact constant/Rlim
  adjunction, quotient completion unit and exact termwise tower pullback, in
  CompletedPullbackInterface. Source: Stacks 079P, 099N and the existing
  construction. Mathlib provides the generic constant/limit and exact-derived
  APIs. No new proof obligation is introduced.

## Forced adaptations

Sheaf.Paper.StratumCompletionUnitRestriction is held by G4. Its only changed
line is line 8: public import Sheaf.Paper.CompletedPullback becomes public import
Sheaf.Paper.CompletedPullbackInterface. Every declaration signature, visibility,
construction body and proof stays identical. Retaining the original import makes
lcompile.py --all fail before compilation with:
"the modules import one another in a cycle: Sheaf.Paper.CompletedPullback,
Sheaf.Paper.CompletedPullbackReduction, Sheaf.Paper.CompletedTowerDirectImage,
Sheaf.Paper.CompletedTowerPullback, Sheaf.Paper.StratumCompletionUnitRestriction".
The two extra consumers were temporarily present for the return verification;
the essential cycle is CompletedTowerPullback -> StratumCompletionUnitRestriction
-> CompletedPullback -> CompletedTowerPullback. import_direction.py confirms the
same cycle in the original shared graph. Replacing only that import makes the
nine-module packet compile, including the adapted stratum module in 5.5 seconds.
A single-file compile of the original can load a previously compiled graph and
is insufficient to validate this cyclic source packet.

## Forced adaptations

### Sheaf.Paper.StratumCompletionUnitRestriction
NOT FORCED: the original compiles unchanged against the changed dependencies. Adapted module compiled in the delivered set; the reader judges whether the change is right.

## Second reading by A4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
