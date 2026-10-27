## Worker report

NB, 2026-10-27. Stage-1 repair of the released six-declaration extraction order.
The parent statement is byte-for-byte unchanged. Six new independently claimable
statement-only nodes have status unsplit, no proof/proof_deps/lean field, and no
claimed proof completion. Four parent assembly steps total 2106 characters.
Every text of the three old parent proof steps occurs verbatim in a new node's
source.note; the original parent JSON is also retained in scratchpad/original-parent.json.
The source.note material is explicitly unproved construction material.

## Files written

- dag/nodes/sec-six-functors/prop-sf-pf-coherence.json: parent assembly and six-name split_report mapping; statement unchanged.
- dag/nodes/sec-six-functors/lem-sf-projection-base-change-common.json: statement; no exact Mathlib match; unsplit.
- dag/nodes/sec-six-functors/lem-sf-projection-base-change-integral.json: statement; no exact Mathlib match; unsplit.
- dag/nodes/sec-six-functors/lem-sf-projection-base-change-rational.json: statement; no exact Mathlib match; unsplit.
- dag/nodes/sec-six-functors/lem-sf-projection-reduction-common.json: statement; no exact Mathlib match; unsplit.
- dag/nodes/sec-six-functors/lem-sf-projection-reduction-integral.json: statement; no exact Mathlib match; unsplit.
- dag/nodes/sec-six-functors/lem-sf-projection-reduction-rational.json: statement; no exact Mathlib match; unsplit.
- report.md, citations.json, searches.jsonl and scratchpad evidence are in this sandbox only.

## Attachments

None. All six requested declarations still have sorry bodies in the current
Sheaf.Paper.ProjectionFormulaCoherence source. The project WeilConjectures finite-etale
coherence theorems cover finite ordinary categories, not the completed, localized
and common-stage obligations. No attachment of a completed proof is claimed.

## WANTED

None for this extraction. Current blueprint statement/proof, the live Lean
headers and their docstrings, and the existing DAG statements are available.
No SGA proof source is used. The unchanged parent retains its inherited historical
SGA reference as required by the explicit unchanged-statement order.

## What was wrong and what was repaired

The old parent owned six distinct unproved higher-coefficient declarations, so
one stage-3 claim serialized them. This repair follows the human's explicit
exception to the usual no-clause-only-split rule: six named source obligations
are separate claimable unsplit nodes, and the parent is their short assembly.
New nodes carry no proof steps and no lean attachments. Exact source allocation
and proposed later proving modules are only sorried lean_candidates and the
parent split_report.lean_declarations mapping; stage 2 must validate and bind them.

At session start the assigned NB sandbox contained only the brief markers.
The NE sandbox named in the maintenance handoff did not exist at its named path.
The maintenance record coord/reports/maintenance/NE-prop-sf-pf-coherence-1793082697.md
and current route note were read. Therefore this packet was reconstructed from
the live source and parent, preserving all live argument text, rather than
claiming possession of the absent NE packet or its old search evidence.

The only matching abandoned directory was
/home/ubuntu/weil-launcher-all/abandoned/Q51/prop-sf-pf-coherence.1792853395.
Its report.md and searches.jsonl were read before new work, then copied unchanged
as scratchpad/Q51-report.md and scratchpad/Q51-searches.jsonl, with Q51 attribution.
Those 2026-10-24 searches are historical evidence, not searches claimed by NB.
The Q51 scope objection compared the newer finite-etale source with the older
four-stage datum. The current explicit 2026-10-27 keep-statement repair order
settles this item's authorized scope: extract the six concrete live headers
without replacing the parent's meaning. No failed mathematical construction or
compilation from Q51 was repeated.

## Lean declarations

All source declarations below are in namespace WeilConjectures, module
Sheaf.Paper.ProjectionFormulaCoherence, file
lean/Sheaf/Paper/ProjectionFormulaCoherence.lean. The same source is present at
quarantine/Sheaf/Paper/ProjectionFormulaCoherence.lean. Each new node records the
full theorem header, exact keyword line, source module/path and quarantine
path/line, proposed separate proving module, and sorried status. No Lean file
was written or compiled, and no existing declaration was moved.

- lem-sf-projection-base-change-common: WeilConjectures.sixFunctorProjection_baseChange_common, source line 648; proposed proving module Sheaf.Paper.ProjectionBaseChangeCommon; sorried.
- lem-sf-projection-base-change-integral: WeilConjectures.sixFunctorProjection_baseChange_integral, source line 523; proposed proving module Sheaf.Paper.ProjectionBaseChangeIntegral; sorried.
- lem-sf-projection-base-change-rational: WeilConjectures.sixFunctorProjection_baseChange_rational, source line 586; proposed proving module Sheaf.Paper.ProjectionBaseChangeRational; sorried.
- lem-sf-projection-reduction-common: WeilConjectures.sixFunctorProjection_reduction_common, source line 1246; proposed proving module Sheaf.Paper.ProjectionReductionCommon; sorried.
- lem-sf-projection-reduction-integral: WeilConjectures.sixFunctorProjection_reduction_integral, source line 1140; proposed proving module Sheaf.Paper.ProjectionReductionIntegral; sorried.
- lem-sf-projection-reduction-rational: WeilConjectures.sixFunctorProjection_reduction_rational, source line 1192; proposed proving module Sheaf.Paper.ProjectionReductionRational; sorried.

## Source and search evidence

For the parent and all six new nodes I read the latest statement and proof at
literature/blueprint/latest/blueprint/sec-six-functors/sk-prop-sf-pf-coherence/,
the full unit record dag/units/sk-prop-sf-pf-coherence.json, chapter record,
and the 2026-10-27 released repair order. The latest link currently resolves to
the main-20261026 snapshot (a8806c1f60d0aec15c57e02339aea4bedc0e3759).
For each base-change node I read its source theorem and its exact Mu/Exchange
definitions at lines 470-673; the integral theorem starts at 523, rational at
586, common at 648. For each reduction node I read its full square definition,
associator normalization and theorem at lines 1083-1253; the integral theorem
starts at 1140, rational at 1192, common at 1246. These headers are the exact
extraction source. The DAG categories are defined by the existing derived-complete,
raw-localization and common-stage definition nodes, all read.

Before creating the nodes I searched the whole DAG by the six source names,
base-change/reduction terminology and anticipated ids, and ran blueprint_refs.py
ancestor and searches for projection, projection integral, projection rational,
projection common, projection base change and projection reduction. The broad
projection results include the parent and generic/finite component results;
none is an independent node owning one of these exact six headers.
The finite ordinary projection coherence and LowerShriekCompositionCoherence
source modules were inspected and do not discharge these higher-stage headers.

Each new node has five actual msearch.py records: its own statement phrasing
in LeanFinder, Loogle, a Mathlib grep, and a second phrasing in LeanSearch and
LeanFinder. Complete returned outputs are in scratchpad/search-00.txt through
search-29.txt with the per-node plan in scratchpad/search-plan.json; the actual
command appended searches.jsonl. All services responded successfully. Returned
hits were inspected: sheaf pullback compositors, condensed monoidal structures,
adic module completion and generic monoidal adjunction identities do not state
the normalized compact-support equations. The proper counit monoidal lemma
suggested by LeanSearch is only a proper-factor candidate, not the completed
proper/open equation. Its exact declaration-name grep in the pinned Mathlib
returned no hit; it is not promoted to a leaf. There are zero Mathlib leaves.

## Not duplicates

lem-sf-projection-base-change-common vs prop-sf-pf-coherence: the human explicitly requests this one named sorried coefficient-stage obligation as an independently claimable node; the parent includes all structural and four-stage clauses.

lem-sf-projection-base-change-common vs lem-sf-pf-open-base-change-square: the existing result gives the open-factor equation and monoidality at finite/integral stages; the new node is the full datum-coordinate compact-support square at the specified higher stage.

lem-sf-projection-base-change-common vs lem-sf-pf-compactification-pasting: the existing lemma is conditional on two factor identities; the new node asserts the unconditional actual coefficient-stage equation with exact comparisons.

lem-sf-projection-base-change-common vs lemma-weil-pbc-projection-formula-base-change-naturality: the existing theorem is ordinary uncompleted direct image for ringed topoi, not completed/localized/common-stage compact support.

lem-sf-projection-base-change-common vs fix-prop-projection-formula: that package neither isolates this header nor supplies an independent proof; its proof_deps explicitly contains the parent, so using it here would be circular.

lem-sf-projection-base-change-integral vs prop-sf-pf-coherence: the human explicitly requests this one named sorried coefficient-stage obligation as an independently claimable node; the parent includes all structural and four-stage clauses.

lem-sf-projection-base-change-integral vs lem-sf-pf-open-base-change-square: the existing result gives the open-factor equation and monoidality at finite/integral stages; the new node is the full datum-coordinate compact-support square at the specified higher stage.

lem-sf-projection-base-change-integral vs lem-sf-pf-compactification-pasting: the existing lemma is conditional on two factor identities; the new node asserts the unconditional actual coefficient-stage equation with exact comparisons.

lem-sf-projection-base-change-integral vs lemma-weil-pbc-projection-formula-base-change-naturality: the existing theorem is ordinary uncompleted direct image for ringed topoi, not completed/localized/common-stage compact support.

lem-sf-projection-base-change-integral vs fix-prop-projection-formula: that package neither isolates this header nor supplies an independent proof; its proof_deps explicitly contains the parent, so using it here would be circular.

lem-sf-projection-base-change-rational vs prop-sf-pf-coherence: the human explicitly requests this one named sorried coefficient-stage obligation as an independently claimable node; the parent includes all structural and four-stage clauses.

lem-sf-projection-base-change-rational vs lem-sf-pf-open-base-change-square: the existing result gives the open-factor equation and monoidality at finite/integral stages; the new node is the full datum-coordinate compact-support square at the specified higher stage.

lem-sf-projection-base-change-rational vs lem-sf-pf-compactification-pasting: the existing lemma is conditional on two factor identities; the new node asserts the unconditional actual coefficient-stage equation with exact comparisons.

lem-sf-projection-base-change-rational vs lemma-weil-pbc-projection-formula-base-change-naturality: the existing theorem is ordinary uncompleted direct image for ringed topoi, not completed/localized/common-stage compact support.

lem-sf-projection-base-change-rational vs fix-prop-projection-formula: that package neither isolates this header nor supplies an independent proof; its proof_deps explicitly contains the parent, so using it here would be circular.

lem-sf-projection-reduction-common vs prop-sf-pf-coherence: the human explicitly requests this one named sorried coefficient-stage obligation as an independently claimable node; the parent includes all structural and four-stage clauses.

lem-sf-projection-reduction-common vs lem-sf-projection-tensor-coordinate-action: the latter concerns ordinary derived sheaves in a generic Grothendieck coefficient category; the new statement concerns the datum's completed, localized or common-stage category and its normalized tensor comparisons.

lem-sf-projection-reduction-common vs lem-pur-system-projection-tensor-associativity: the latter is an equality of normalized strict systems on separated schemes with finite-Tor inputs; it does not assert this completed/localized/common-stage equation for all constructible K,L,N.

lem-sf-projection-reduction-common vs prop-sf-pf-reduction: the existing statement only compares successive positive finite levels on finite-Tor inputs; the new node gives the higher-stage tensor-action identity for arbitrary right tensor object.

lem-sf-projection-reduction-common vs fix-prop-projection-formula: that package neither isolates this header nor supplies an independent proof; its proof_deps explicitly contains the parent, so using it here would be circular.

lem-sf-projection-reduction-integral vs prop-sf-pf-coherence: the human explicitly requests this one named sorried coefficient-stage obligation as an independently claimable node; the parent includes all structural and four-stage clauses.

lem-sf-projection-reduction-integral vs lem-sf-projection-tensor-coordinate-action: the latter concerns ordinary derived sheaves in a generic Grothendieck coefficient category; the new statement concerns the datum's completed, localized or common-stage category and its normalized tensor comparisons.

lem-sf-projection-reduction-integral vs lem-pur-system-projection-tensor-associativity: the latter is an equality of normalized strict systems on separated schemes with finite-Tor inputs; it does not assert this completed/localized/common-stage equation for all constructible K,L,N.

lem-sf-projection-reduction-integral vs prop-sf-pf-reduction: the existing statement only compares successive positive finite levels on finite-Tor inputs; the new node gives the higher-stage tensor-action identity for arbitrary right tensor object.

lem-sf-projection-reduction-integral vs fix-prop-projection-formula: that package neither isolates this header nor supplies an independent proof; its proof_deps explicitly contains the parent, so using it here would be circular.

lem-sf-projection-reduction-rational vs prop-sf-pf-coherence: the human explicitly requests this one named sorried coefficient-stage obligation as an independently claimable node; the parent includes all structural and four-stage clauses.

lem-sf-projection-reduction-rational vs lem-sf-projection-tensor-coordinate-action: the latter concerns ordinary derived sheaves in a generic Grothendieck coefficient category; the new statement concerns the datum's completed, localized or common-stage category and its normalized tensor comparisons.

lem-sf-projection-reduction-rational vs lem-pur-system-projection-tensor-associativity: the latter is an equality of normalized strict systems on separated schemes with finite-Tor inputs; it does not assert this completed/localized/common-stage equation for all constructible K,L,N.

lem-sf-projection-reduction-rational vs prop-sf-pf-reduction: the existing statement only compares successive positive finite levels on finite-Tor inputs; the new node gives the higher-stage tensor-action identity for arbitrary right tensor object.

lem-sf-projection-reduction-rational vs fix-prop-projection-formula: that package neither isolates this header nor supplies an independent proof; its proof_deps explicitly contains the parent, so using it here would be circular.

## Review by NB

I compared the six source theorem headers with the six TeX statements and checked
the actual operation coordinates rather than substituting arbitrary isomorphic
functors. The base-change equation has source U_g(FK tensor L) and target
F'(U_g'K tensor U_f'U_gL). On its left route the pullback tensor comparison is
followed by the inverse compositor, square equality, and forward compositor;
on its right route the tensor exchange precedes the bottom projection. This is
the same ordering as the exact source headers. Integral base change restricts
only L to the uniform finite-reduction Tor predicate; K is arbitrary bounded
constructible. Rational and common base change have no extra Tor predicate.
The compactified square includes the chosen open/proper factors and their
Cartesian base changes. I did not add separatedness of g or structure maps.

For reduction I checked each predicate definition, not just the theorem name.
All three statements quantify over arbitrary K,L,N in their recorded constructible
categories. The left composite has source (FK tensor L) tensor N and target
F((K tensor UL) tensor UN). The right composite first applies the target
associator, then one projection at L tensor N, then the image of the pullback
tensor comparison, then the separate image of the inverse source associator.
Thus I retained the exact arbitrary-N theorem rather than shrinking it to
constant quotients or imposing finite-Tor assumptions. Integral operations are
completed, rational operations are raw localizations, and common objects/maps
use one finite coefficient field. No reduction of a field object to a finite
coefficient ring is asserted.

For assembly step 1 I read all three stage-law statements and identity assembly.
The stage laws explicitly contain input naturality, compactification independence,
composition, pentagon and proper coincidence; identity assembly supplies exactly
the normalized identity equation on the indicated four-stage domains. This
step uses their statements, not a construction hidden in their proofs.

For step 2 I read def-sf-finite-base-change-realization-paths and
lem-sf-finite-base-change-transport: their statements give exactly the left and
right routes and their equality. Each new base-change statement gives the full
higher-stage equation, including the comparison maps just checked. The exchange
statement fix-lem-exchanges gives square/refinement naturality on its stated
domains; coupled with step 1's projection independence this identifies the
compactification presentations. Its generic use is recorded as a tool use.

For step 3 I read def-sf-constructible-projection-mates, whose statement explicitly
constructs the actual finite arrow by realization conjugation through the full
inclusion, and lem-sf-projection-tensor-coordinate-action, which states the
entire associator/pullback comparison equation for arbitrary derived sheaves.
Conjugation cancellation is elementary; the tensor-action identity is the
cited theorem. The degree-zero constant A/J is a permitted arbitrary derived
coefficient object; no perfectness or flatness of A/J is used. This avoids the
old mistake of taking an all-ideal assertion from prop-sf-pf-reduction, whose
actual statement only treats successive positive levels on finite-Tor inputs.

For step 4 I read the three new arbitrary-N reduction statements and the full
lem-sf-pf-coefficient-realization-transport statement, including intertwining of
primitive units, counits, open maps, tensor and pullback comparisons, full-domain
closure and comparison cocycles. The needed datum comparisons are those of
A5 and def-exchange-projection; this step is transport through these specified
data, not an existence claim for comparison data. thm-sf-pf-field explicitly
identifies rational and common-stage components via integral representatives;
thm-sf-pf-proetale identifies the realized proper/open components. These are
the precise facts used; no faithfulness of finite evaluation is inferred.
Every use has a verbatim statement quote in citations.json, including qualifiers.

I checked delivery-errors B-E explicitly. All six nodes introduce their own
coefficient, geometric, categorical and map data with TeX written once and
existing definition-node references. They have no proof/proof_deps/lean fields.
Their from.node is the nearest ancestor prop-sf-pf-coherence; from.place names
the displayed square or last tensor-reduction clause, and same_as is searched.
The explicit six-obligation repair order authorizes the otherwise forbidden
clause extraction, and all original arguments are retained rather than blurred.
All parent proof dependencies equal the union of uses. No step exceeds 2000
characters and no unidentified inline lemma was moved into a long assembly.

I tested the statements on identity squares, identity compactifications and
identity coefficient extensions: both base-change routes have the same
canonical unit/compositor transports. Empty schemes and zero inputs preserve
the types and give zero composites. For tensor action, N=0 gives zero maps,
N the coefficient unit gives the unit identity, J=0 gives identity reduction,
and J=Lambda gives the zero quotient. Over a field these are the only ideal
quotients, while the theorem still retains arbitrary nonconstant N. At finite
coefficients nonperfect quotients remain ambient, so no false claim of finite-Tor
preservation is introduced. These are source/type and mathematical checks,
not compilation or proof certification.

## Unfinished work

All six new obligations remain unproved and deliberately unsplit, as required
by stage 1. Their full headers, source notes and proposed separate modules allow
later workers to split/prove them independently. No source or target statement
has been weakened, no Lean was written, no compiler/Lake/build was run, no
repository or launcher file was changed, and no agent was started.

## Dry-run repair

The first ordinary dry run exited with only B4 findings on the three new
base-change diagrams: a valid TeX row break immediately followed by the next
row's letter matched the literal doubled-command detector. I put each diagram
row on its own line, retaining exactly the same square, and corrected an
accidental raw-string apostrophe escape. The parent statement remains unchanged.
The three retained stage-law interfaces are explicitly declared generic tools
in split_report.tool_uses; they assemble structural laws without replacing
the unit's proper/open route. The new nodes still have no proof steps or lean
attachments. All updated citation quotes were recopied from the statements.

## Returned landing repair — 2026-10-27

The reader approved the mathematical packet, but the landing refused its fix to
dag/units/sk-prop-sf-pf-coherence.json because that file was absent from the
delivery. The stage-1 contract explicitly allows this key node to set its unit's
realized and realized_by fields. I now include that unit record in the delivery,
register all six separately claimable obligations alongside the existing realizers
of its sole proof step, retain prop-sf-pf-coherence as its statement realizer,
and update realized_by. The unit's statement, proof text, uses, chapter and all
other fields are copied from the current live DAG without change. This is the
concrete repair; it is not an unchanged re-push.

I compared the retained parent with the current live node. Its only pre-repair
differences were the approved proof, proof_deps, proof_origin and split_report.
No cited current statement changed: each was opened and compared in full with
its retained verbatim quotation; the per-citation SHA256 comparison is saved in
scratchpad/landing-repair-citation-comparison.json. Thus the four approved
assembly steps and six unsplit statements require no mathematical revision.
The parent statement remains byte-for-byte unchanged. No Mathlib searches were
repeated because neither the six statements nor their search questions changed;
all original raw search records and their attribution remain in the sandbox.
The normal deliver.py packager rebases the packet on the current origin/sheaf-dag
and preserves all maintainer-owned node and unit fields.

The additional delivered file is dag/units/sk-prop-sf-pf-coherence.json; only
realized and realized_by differ from the current live unit. The parent
split_report records this repair and the six added unit realizers. There remain
six new statement-only unsplit nodes and zero Mathlib leaves. The Review by NB
above continues to cover the approved assembly and source obligations; this
repair additionally checks the unit realization against its one source proof
step and the explicit six-declaration allocation. No Lean file, compiler or
protected tool was involved.
