## What changed

Repaired Sheaf.Paper.CechCupPullbackCompat without changing any existing public
signature, definition or public import. Coefficient naturality is proved from the
existing moduleCup_coefficient_resolution_maps theorem: choose computing cycles,
transport all three through the coefficient cochain maps, use the strict pairing
identity, and apply the two cup characterizations. The private cocycle helper now
uses cycle_val_d for each input differential rather than separately expanding the
kernel's successor index. It constructs the paired cocycle directly by Leibniz.

The composition comparison square applies cechRefinement_comparison_square directly,
removing the unused comparison-map import and auxiliary product constructions.
The existing node's proof route and dependencies match this proof.

## Proved and sorry left

The current delivery base has two holes. Closed one:
AlgebraicGeometry.Scheme.Modules.moduleCup_coefficient_naturality.
No holes added; no split statements or new nodes. Five already proved public
theorems are retained. This leaves six of seven public theorem bodies filled.

The sole remaining sorry is
AlgebraicGeometry.Scheme.Modules.moduleCup_pullback_naturality
(lem-sc-picard-cech-cup-pullback-compat), unchanged as a statement and retained as
the original named theorem with its source and proof in words.

## No longer needed

Removed import Sheaf.Paper.CechComparisonMapNaturality and proof dependency
lem-sc-cech-comparison-map-naturality: composition uses the supplied comparisons
and the refinement comparison square directly. No whole-closure pruning claim
is made for this module, which can still have other users.

The obsolete pullback-resolution import from the returned delivery is absent.
No replacement hole is introduced. ModuleCupPullbackCycleStep is not imported or
delivered: its historical unchanged source imports this item, and importing it
back would be circular. It is kept solely as scratch validation material because
it is absent from the current repository. Neither collision dependency,
ModuleCupNaiveDerivedCompatibility nor GlobalTensorPullbackMonoidalNormalization,
is added by this repair. Their instances are not changed.

## Where the brief, the DAG or earlier work was wrong

The return describes an older two-module delivery. The supplied sandbox already
contains a subsequent partial repair, and the current repository has no source
for ModuleCupPullbackCycleStep. This repair preserves that module's historical
signature and proof as validation material rather than delivering it as a new
module or importing it back. The change in this session is the cocycle helper's
use of the already proved cycle_val_d API; the coefficient proof remains complete.

Return points addressed:

1. Main-module axiom probe collision: the delivered proof uses the existing
   coefficient-resolution interface, with no obsolete pullback-resolution import.
   The delivery dry run compiles and probes this actual import graph.
2. Main-module importer failures: every existing public signature, definition,
   and public import is preserved. Only private helpers, proof imports and proof
   bodies differ. The original declarations used downstream remain available.
3. CycleStep changing its importer: no CycleStep change is delivered and the main
   module does not import it. No interface adaptation is required.
4. CycleStep axiom-probe collision and self-importer failure: the historical
   unchanged source is validated against the repaired main module in scratch,
   without changing either dependency's instance or delivering the removed module.

Validation of the edited source: main module compiled in 45.2 seconds; unchanged
PicardExternalCupLeftComparisonComplexes, PicardExternalCupRightCechDiagram,
PicardScalarCechExternalCup and historical ModuleCupPullbackCycleStep compiled
against its freshly generated output in 4.7, 4.5, 6.0 and 6.1 seconds respectively.
All five files had exit code 0 without errors or warnings. The declaration parser
reports no statement changes or added sorry declarations; the node's proof_deps
is the exact union of its proof-step uses. All delivered Lean lines are at most
100 characters. A combined scratch import of the repaired main module and the
historical unchanged CycleStep compiled in 1.6 seconds and ran all three explicit
axiom prints: coefficient naturality uses only propext, Classical.choice and
Quot.sound; pullback naturality and CycleStep retain the documented sorryAx from
the unchanged pullback hole. The duplicate-instance import error did not occur.

The earlier report's second-reading section is retained below as historical
review of the prior partial repair. The next reader should recheck the small
cocycle-helper edit and the final validation results recorded above it.

## Earlier second reading (a previous round; superseded)

1. **Interface preservation — pass.** Compared the item and the validation-only CycleStep copy with the
   repository snapshot. The declaration parser confirms all 17 existing declarations of
   CechCupPullbackCompat have identical signatures and visibility. Definitions,
   public imports, and existing docstrings are unchanged. The CycleStep copy was
   byte-for-byte identical and used only for downstream compilation. It was
   subsequently moved to scratchpad and is excluded from the delivery.
2. **Proof validity — pass.** Read the coefficient proof and its two new private,
   fully proved helpers. The computing class map is a composite of surjections;
   the section pairing of cocycles is a cocycle by Leibniz. Cochain maps transport
   the three cycles, the resolution theorem supplies the three class equations
   and strict pairing equation, and the two cup characterizations finish the
   equality. No data is defined using an arbitrary unproved existence witness:
   the resolution witnesses are eliminated inside a theorem proof. The complete
   sandbox compiled in import order (49.6 seconds and 6.3 seconds), with no errors
   or warnings. The sole remaining sorry is the original public
   moduleCup_pullback_naturality; no forbidden declaration or hollow definition
   occurs. A scratch copy compiled in 44.6 seconds and printed axioms for all seven
   public theorem declarations. moduleCup_coefficient_naturality,
   cechRefinement_coefficient_naturality, cechCup_coefficient_naturality, and
   cechCup_refinement_naturality use only propext, Classical.choice, and
   Quot.sound. cechCupPullbackCompat and cechRefinement_composition_naturality
   additionally use sorryAx from still-open dependencies; the remaining
   moduleCup_pullback_naturality also uses sorryAx. The delivery probe
   additionally checks all declarations.
3. **Split statements — pass, none added.** No new public statements, new nodes,
   or split-off holes. Searched the project and upstream sources for coefficient
   and pullback cup naturality, and used msearch grep with a different query. The
   surjectivity and Leibniz helpers also occur as private declarations in
   ModuleCohomologyCupProduct; they are inaccessible here, and both local copies
   are fully proved. Their arguments apply at p=0 or q=0 and to zero cocycles:
   next n is always n+1, and bilinearity kills both Leibniz summands. CycleStep
   cannot close the remaining pullback hole: it applies that very theorem, so
   importing it back would be circular.
4. **Route and pruning — pass.** The coefficient proof uses the existing
   coefficient-resolution theorem rather than adding a duplicate reduction.
   Composition uses the refinement comparison square directly. Every retained
   proof import has an explicit use, and the only old proof dependency removed
   is lem-sc-cech-comparison-map-naturality, already listed above. No claim is
   made that its module disappears from the whole targets closure. The unit
   sk-prop-av-cube and its realized record are unchanged; this work remains
   below its fixed route. Six of seven theorem bodies are now filled, closing
   one of the two original holes; no holes are added. Imported open statements
   still prevent treating all these declarations as axiom-free target proofs.
5. **DAG agreement — pass after repair.** Parsed the node against its repository
   counterpart: only proof, proof_deps, and proof_origin differ. proof_deps is
   exactly the union of step uses. The coefficient step matches the actual
   cycle-transport proof; comparison composition no longer constructs auxiliary
   cup products. No new-node fields or change records are required.

Second-reader changes: excluded the unchanged CycleStep validation copy from the
delivery after the refreshed server base removed that module; removed a stale heartbeat override and comment beside the
remaining sorry (there are no cycle transports in that body); corrected the DAG's
stale claim that both sheaf-cup naturalities remain unproved and its historical
comparison-square description; removed unused cup-product uses from the
composition step (the same dependencies remain needed by other steps). No correct
proof body was rewritten, no signature was changed, and no additional hole closed.

The first second-reader dry run passed (3c5400afa7). During the push attempt,
preflight refreshed the base and classified the formerly unchanged CycleStep copy
as a new module, refusing it without a new node. It is validation material, not
a new result, so it was moved out of lean/ instead of introducing a node. The
item does not import it; this removes no dependency of the reviewed proof.

## Second reading by V4

1. **Interfaces — pass.** Independently diffed the sole delivered Lean module against
   the repository. The declaration parser reports no changed existing signatures
   or added sorry declarations. Existing definitions, visibility, public imports
   and docstrings are unchanged. The only removed import is proof-only.
2. **Proof — pass.** Read the module, including the coefficient proof and the
   composition comparison calculation. The resolution class map is a composite
   of the surjective kernel projection and two isomorphisms. The paired cycle is
   constructed explicitly from the two input cycles, with its differential killed
   by cycle_val_d and Leibniz. The resolution witnesses are eliminated inside the
   theorem proof, not used to define arbitrary data. The three transported cycles
   satisfy the strict pairing identity and computing-class equations; the source
   and target cup characterizations finish the equality. Local compilation passed
   without warnings in 36.2 seconds. The sole sorry is the original named
   moduleCup_pullback_naturality with its unchanged source and proof docstring.
   No forbidden declaration or hollow definition occurs.
3. **Split statements — pass, none.** No split statements or nodes were added.
   Independently searched with msearch grep for base change, inverse image and cup
   naturality, and searched the project and upstream Mathlib sources. No direct
   shorter theorem was found. The two new private helpers also have private copies
   in ModuleCohomologyCupProduct and ModuleCupRealizationEvaluation; they cannot
   be used as public APIs. Their proofs hold for p=0, q=0, zero input cycles and
   zero coefficient maps: successor differentials remain defined and linearity
   kills the zero Leibniz summands. No flatness or extra cover condition is used.
4. **Route and pruning — pass.** The existing coefficient-resolution theorem is
   used directly, with a real cycle-level reduction. The composition comparison
   uses cechRefinement_comparison_square on the supplied maps, dispensing with
   comparison-map existence and auxiliary cup products. The removed old dependency
   lem-sc-cech-comparison-map-naturality is completely listed in No longer needed.
   Each retained proof import has an explicit use; the public imports supply
   notions in the existing signatures. The unit sk-prop-av-cube and its realized
   record are untouched. One of the two original holes is closed, none added;
   this is not a decomposition or a claim that imported open proofs are closed.
5. **DAG — pass.** Parsed and compared both node versions: only proof, proof_deps
   and proof_origin changed. The union of the proof-step uses is exactly
   proof_deps. The coefficient step describes the actual cycle construction and
   transport, and composition describes the direct comparison-square route.
   No new-node fields or statement change records are required.

Second-reader changes: no Lean or DAG repair was needed. Replaced the scratch
axiom copy with the exact current module and appended this independent review.
The obsolete CycleStep remains outside the delivered lean directory.

Independent current-source axiom validation: the scratch copy compiled cleanly
in 35.0 seconds. Explicit #print axioms for all seven public theorem declarations
shows only propext, Classical.choice and Quot.sound for coefficient naturality,
Cech coefficient naturality, refinement coefficient naturality and Cech refinement
naturality. cechCupPullbackCompat and refinement composition additionally use
sorryAx from existing open dependencies; moduleCup_pullback_naturality retains its
own original sorryAx. No other axiom occurs.
