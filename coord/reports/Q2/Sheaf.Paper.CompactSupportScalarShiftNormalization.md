## What changed

Replaced the proof of WeilConjectures.PurStrictScalar.compactSupportScalarShiftNormalization
by an assembly of actual natural-transformation shift squares, using the existing
compactSupportScalarLimitReduction factorization and completeness conclusions.
The theorem statement, all canonical shifts, and every comparison map are unchanged.
The original shift instances and OriginalMateShift predicate moved verbatim to the
publicly re-exported CompactSupportScalarShiftStructures module to permit acyclic
imports of the four smaller proof steps. No source-library declarations change.

Ordinary tensor-shift uniqueness is proved using a generic localization lemma:
cancel the invertible localization shift and factor map, use localization
natural-transformation extensionality, and identify the CommShift structures.
Completed/finite scalar normalization uniqueness reuses the already proved
scalarCommShift_existsUnique helper. The main proof combines these two arguments
with original-site, strict-site and scalar-limit constraint interfaces, and the
final normalized witness clause, by conjunction introduction.

The final witness clause is compactSupportScalarShiftWitness (Steps 5--9).
It asserts existence, exact factorization and the three actual component shift
equations, without any of the original or strict constituent CommShift clauses,
normalization-uniqueness clauses or individual scalar-limit constraint clauses.
Its docstring gives the factorization/full-faithfulness descent argument.

Change record: coord/changes/Q2-compact-support-scalar-shift-interfaces.md.

## Proved and sorry left

The original module had one sorry: compactSupportScalarShiftNormalization.
Its proof is now complete modulo four strictly smaller auxiliary theorems;
this is a decomposition, not a net reduction in holes. Original holes closed: 1.
New holes added: 4. Remaining original holes: 0. Net: -3.

The four new public theorem holes, each exactly `:= by sorry`, are:

- WeilConjectures.PurStrictScalar.originalScalarMateShift,
  node lem-pur-original-scalar-mate-shift.
- WeilConjectures.PurStrictScalar.strictScalarMateShift,
  node lem-pur-strict-scalar-mate-shift.
- WeilConjectures.PurStrictScalar.scalarLimitConstraintShift,
  node lem-pur-scalar-limit-constraint-shift.
- WeilConjectures.PurStrictScalar.compactSupportScalarShiftWitness,
  node lem-pur-compact-support-scalar-shift-witness.

Each theorem has the precise canonical functors and maps in its statement, source
references and a complete natural-language proof in its docstring and DAG node.
No postponed data construction is added. The extracted instances are unchanged.

## No longer needed

The following private imports are removed from the main module because their
chain/resolution arguments are now owned by the named auxiliary nodes:
Sheaf.CategoryTheory.CompactSupportRoosCofinality,
Sheaf.Algebra.Homology.DerivedTensorAdditiveConstraints,
WeilConjectures.CategoryTheory.RightKanExtensionCoherentShift,
Sheaf.CategoryTheory.LocalizedModuleExactForSystems,
Sheaf.CategoryTheory.StrictRoosDerivedLimitComparison,
Sheaf.Paper.CompletedScalarChainShift,
Sheaf.Paper.IntegralScalarExtensionWellDefined,
Sheaf.Paper.ConstantCompletionEquivalence,
Sheaf.Paper.DerivedAdjunctionShift,
Sheaf.CategoryTheory.DiagramSiteRealization,
Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients,
Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses,
Sheaf.CategoryTheory.ProductCommShift,
Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact,
Sheaf.Algebra.Homology.RoosCommShift.

All nineteen original public prerequisites are retained through the extracted
structures module. No module is withdrawn. The original 22 proof dependencies
are retained where relevant in the four new argument steps; the parent now cites
the smaller interfaces. No global pruning is claimed. In particular the signed
Roos, constant/completed equivalence, and diagram-site arguments remain required.

## Where the brief, the DAG or earlier work was wrong

Existing scalarCommShift_existsUnique already proves universal-counit uniqueness;
this should not be recreated as a new hole. Its enclosing coefficient-comparison
node depends on the present item, so a separate attachment records this proved
helper without adding the parent theorem as a circular proof dependency. Likewise
the actual-predicate integralTriangulated helper is recorded separately rather than
citing the later exceptional-adjunction theorem node. The proof uses only these
proved helpers, never those parent conclusions.

The existing node's high-level steps do not directly state the needed CommShift
interfaces for the actual original-site and diagram-site maps or the completed
gamma descent. Those are precisely the four remaining proof steps.
A dependency traversal also exposes inherited global statement cycles through
compact-support constructibility and coefficient comparison; these are already
present below the original item's statement dependencies. This packet does not
change those unrelated nodes or use the later parent conclusions in Lean.
The declaration's statement is not disputed or weakened. Edge cases checked in
the written arguments: zero objects; identity coefficient extension; r=0 and
negative r; e=1; and e=0 for forward restriction alone, which does not assert an
inverse. No unit route is bypassed.

## New nodes

lem-pur-original-scalar-mate-shift states the original-site proper/open and balanced
comparison/counit squares, following original Steps 2--4.

lem-pur-strict-scalar-mate-shift states their diagram-site analogues and the whole
strict support arrow square, following Steps 2--5, before evaluating levels.

lem-pur-scalar-limit-constraint-shift states the canonical completion, tensor/limit,
arithmetic restriction and support/limit squares, following Steps 6--8.

lem-pur-compact-support-scalar-shift-witness states only the final normalized
gamma witness and its component squares. It uses the stated scalar-limit
factorization, completeness, canonical constraint squares, triangulated closure
and faithful constant/completed descent. It is a proper part of the original
conjunction and leaves the independent uniqueness arguments proved in the parent.

All four have one new module and one named public sorry. Searches used LeanFinder,
Loogle, LeanSearch, local source grep and blueprint searches. Only component APIs
were found, and the reusable ones are used by the main proof.

def-pur-compact-support-scalar-shift-structures records the unchanged extracted
canonical instances and OriginalMateShift predicate; no hole is introduced.

lem-pur-scalar-counit-shift-unique attaches the existing proved
WeilConjectures.PurCompactSupport.scalarCommShift_existsUnique helper.

lem-pur-integral-ctf-shift-closure attaches the existing proved
WeilConjectures.ConstructibleExceptionalCoefficients.integralTriangulated helper
on the actual uniform integral finiteTorConstructibleIntegral predicate.

All new nodes inherit the item's chapter and unit. The interface extraction is
recorded in coord/changes/Q2-compact-support-scalar-shift-interfaces.md.

Delivery verification: all six Lean modules compiled in deliver3.py. The server
preflight refused five newly added parent proof edges because their descendants
reach this item through pre-existing DAG dependency cycles. Representative paths:

def-pur-compact-support-scalar-limit-maps ->
lem-pur-compact-support-strict-scalar-mate ->
def-weil-integral-rational-qbar-compact-support ->
lem-qcqs-compact-support-normalized-lift ->
lem-pur-compact-support-integral-coefficient-comparison ->
lem-pur-compact-support-scalar-shift-normalization.

The original parent already names the strict scalar mate and integral compact
support node among its statement dependencies. The extracted definitions and
new statements use those same actual objects. Dropping those edges would conceal
required definitions. No Lean import cycle exists, and tools/import_direction.py
accepted the only extra proof import; tools/downstream.py found zero importers.
This needs maintainer reconciliation of the pre-existing definition/proof DAG
attachments. No packet was pushed. The sandbox preserves the compiling reduction.

Resumed-attempt verification (2026-10-25): ran the required deliver3.py command
against the current sources. It again reached server preflight, then refused
exactly five added proof dependencies of the parent:
def-pur-compact-support-scalar-shift-structures,
lem-pur-compact-support-scalar-shift-witness,
lem-pur-original-scalar-mate-shift,
lem-pur-scalar-limit-constraint-shift, and
lem-pur-strict-scalar-mate-shift. Nothing was pushed.

An independent read-only traversal of the current repository alone, without any
sandbox nodes, confirmed this existing cycle (the edge kind is in parentheses):

lem-pur-compact-support-scalar-shift-normalization
-> lem-pur-compact-support-strict-scalar-mate (stmt_deps and proof_deps)
-> def-weil-integral-rational-qbar-compact-support (stmt_deps)
-> lem-qcqs-compact-support-finite-comparison (proof_deps)
-> lem-pur-compact-support-integral-coefficient-comparison
   (stmt_deps and proof_deps)
-> lem-pur-compact-support-scalar-shift-normalization (proof_deps).

The new structures and auxiliary statements refer to actual functors and maps
already attached along these paths; removing their dependencies would hide those
interfaces. The current theorem signature was compared textually with the
retained packet and agrees. The extracted declaration block also agrees, apart
from the added blueprint attachment in OriginalMateShift's docstring. The unit
record sk-thm-sf-compatibility was checked; no unit record is changed. The gate
and launcher scripts were not modified, and no required dependency was suppressed.
The retained packet therefore still needs maintainer/tool-owner reconciliation
of the inherited DAG cycle before delivery can reach independent review.


Third-attempt verification (2026-10-25): the required initial deliver3.py run
completed with exit code 1 and exactly the same five category-(b) cycle findings
listed above. It explicitly reported "PREFLIGHT FAILED, nothing pushed". The
four-sorry split policy printed a note, not a refusal. No compiler diagnostic
or additional failing preflight category was reported.

The current shared repository, read without any sandbox overlay, also contains
the shorter cycle:

lem-pur-compact-support-scalar-shift-normalization
-> def-weil-integral-rational-qbar-compact-support (stmt_deps)
-> lem-qcqs-compact-support-normalized-lift (proof_deps and proof uses)
-> lem-pur-compact-support-integral-coefficient-comparison (stmt_deps)
-> lem-pur-compact-support-scalar-shift-normalization (proof_deps and proof uses).

The current edge_fails implementation in tools/stage3_delivery.py documents
that a cycle not created by the delivery should not block it. Its test for an
added parent-to-intermediate edge nevertheless requires both endpoints to be
mutually reachable in the base graph. A genuinely new intermediate node cannot
be reachable there, even when its return path merely subdivides the existing
cycle above. This explains the five diagnostics; the structures node and the
four smaller proof steps all require the actual existing definitions.

This attempt rechecked the main theorem signature against the shared source
(textually identical), all six retained Lean files (zero holes in the main and
structures modules; one hole in each of the four split modules), the current
unit record and latest blueprint unit text, and the interface change record.
No Lean, DAG, launcher or project-tool file was changed in this attempt, and
no delivery was retried merely to wait out the reference clock. The compiling
packet remains intact for maintainer/tool-owner reconciliation.


Fourth-attempt verification (2026-10-25): started with the required retained-packet
`deliver3.py Q2 Sheaf.Paper.CompactSupportScalarShiftNormalization` check. It exited
1 with exactly the same five category-(b) dependency-cycle refusals and the explicit
message "PREFLIGHT FAILED, nothing pushed". The four split-off holes were noted,
not refused. No other failing preflight category was reported.

A fresh read-only traversal of the current shared DAG, without sandbox nodes,
confirmed this existing cycle:

lem-pur-compact-support-scalar-shift-normalization
-> def-weil-integral-rational-qbar-compact-support
-> lem-qcqs-compact-support-finite-comparison
-> lem-pur-compact-support-integral-coefficient-comparison
-> lem-pur-compact-support-scalar-shift-normalization.

The current main theorem signature matches the retained packet textually. Actual
hole counts remain zero in the main and structures modules and one in each of
OriginalScalarMateShift, StrictScalarMateShift, ScalarLimitConstraintShift, and
CompactSupportScalarShiftWitness. The refused new edges retain actual canonical
structures and strictly smaller proof interfaces, rather than using a later
parent conclusion as a Lean dependency.

Read tools/stage3_delivery.py:559--593 without changing it: its stated policy is
that an existing cycle must not block a delivery, but its base-graph test requires
the new intermediate node to be mutually reachable before that node exists.
The packet therefore still encounters the inherited-cycle gate failure. No Lean
or DAG dependency was suppressed, no launcher/project tool was edited or bypassed,
and no unchanged delivery was retried. Only this verification note was added;
the retained proof packet is preserved for tool-owner reconciliation.


Fifth-attempt verification (2026-10-25): the required initial
`deliver3.py Q2 Sheaf.Paper.CompactSupportScalarShiftNormalization` check exited 1.
Server preflight again reported exactly the same five category-(b) cycle findings
and "PREFLIGHT FAILED, nothing pushed". The four split-off sorries were an
explicit non-refusal note. No new failing category or compiler error appeared.

A fresh traversal of the current shared DAG, with no sandbox overlay, verified
each edge of the four-edge inherited cycle recorded in the third attempt:
normalization -> integral/rational compact-support definition (stmt_deps)
-> normalized lift (proof_deps) -> integral coefficient comparison (stmt_deps)
-> normalization (proof_deps). The retained theorem signature still matches the
shared source textually. Actual hole counts remain zero in the main and
structures modules and one in each of the four auxiliary theorem modules.

Read the current tools/stage3_delivery.py edge_fails implementation without
editing it. Its base-graph exception still requires both endpoints of an added
edge to be mutually reachable in the base, so a newly introduced intermediate
node cannot qualify even where its return path passes through the existing
cycle. Correcting this policy belongs to the tool owner. Removing the required
statement dependencies would conceal the actual canonical functors and maps.
No Lean/DAG dependency, launcher script or project tool was changed or bypassed;
no unchanged delivery was retried. The retained packet is preserved, with this
verification note as the only sandbox change in this attempt.


Sixth-attempt verification (2026-10-25): ran the required initial deliver3.py
command against current shared sources. It exited 1 at server preflight with the
same five category-(b) dependency-cycle findings and the explicit message
"PREFLIGHT FAILED, nothing pushed". The four split-off sorries were a note,
not a refusal. No additional failing preflight category was reported.

A fresh read-only traversal of the shared DAG confirmed every edge of the
four-edge cycle recorded above: normalization -> integral/rational compact-support
definition (stmt_deps) -> normalized lift (proof_deps) -> integral coefficient
comparison (stmt_deps) -> normalization (proof_deps). The main theorem signature
still matches the shared source textually. Actual hole counts are unchanged:
zero in the main and structures modules, one in each of the four auxiliary
theorem modules.

The current edge_fails implementation at tools/stage3_delivery.py:559 still
requires both endpoints of an added edge to be mutually reachable in the base
graph to qualify for its existing-cycle exception. A new intermediate node
cannot satisfy that test. The retained structures node genuinely needs the
existing canonical scalar-support definitions. No required dependency was
suppressed, and no Lean, DAG, project-tool or launcher file was edited. Only this
verification note was added. The proof packet remains preserved pending
maintainer/tool-owner reconciliation of the inherited-cycle gate failure.


Seventh-attempt verification (2026-10-25): the required initial deliver3.py run
exited 1 at server preflight with the same five category-(b) cycle refusals and
"PREFLIGHT FAILED, nothing pushed". The split-off-sorry policy was explicitly
a note, not a refusal. No other failing category was reported.

A fresh traversal of the shared DAG alone confirmed the four-edge inherited
cycle: normalization -> integral/rational compact-support definition (stmt_deps)
-> normalized lift (proof_deps) -> integral coefficient comparison (stmt_deps)
-> normalization (proof_deps). The main theorem signature still matches current
shared sources textually. The main and structures modules each contain zero
sorry tokens; each of the four auxiliary modules contains one. The current claim
is held by Q2; neither rework.tsv nor returns/Q2.md contains an item-specific
entry. The unit record is unchanged.

Read the current tools/stage3_delivery.py edge_fails implementation: the existing-
cycle exception still requires mutual base-graph reachability for the endpoints
of an added edge, which a new intermediate node cannot satisfy. No required
dependency was suppressed, and no Lean, DAG, launcher or project-tool file was
changed or bypassed. Only this report note was added. The retained packet needs
maintainer/tool-owner reconciliation before delivery can reach review.

Eighth-attempt verification (2026-10-25): the required initial deliver3.py check
exited 1, reporting exactly the same five category-(b) dependency-cycle refusals
and "PREFLIGHT FAILED, nothing pushed". The four new theorem holes were explicitly
a non-refusal note. No additional failing category was reported.

A fresh JSON traversal of the shared DAG, without sandbox overlays, verified
all four edges of the inherited cycle: normalization -> integral/rational
compact-support definition (stmt_deps) -> normalized lift (proof_deps) -> integral
coefficient comparison (stmt_deps) -> normalization (proof_deps). All five rejected
helper destinations remain absent from the base DAG. The current edge_fails
implementation still requires mutual base-graph reachability of the endpoints
for its inherited-cycle exception, which these new destinations cannot satisfy.

Rechecked the retained six Lean files, current theorem signature, current claim,
unit record and latest blueprint unit text. The theorem signature is textually
unchanged. Actual holes remain zero in the main and structures modules and one
in each of the four auxiliary modules. No required dependency was removed, and
no Lean, DAG, project-tool or launcher file was modified or bypassed. Only this
verification note was added. The packet remains preserved pending tool-owner
reconciliation of the inherited-cycle check.


Ninth-attempt verification (2026-10-25): the required retained-packet deliver3.py
check exited 1 with exactly five category-(b) inherited-cycle refusals and
"PREFLIGHT FAILED, nothing pushed". The four added theorem holes were explicitly
a note, not a refusal. No additional failing preflight category was reported.

A fresh JSON traversal of the current shared DAG, without the sandbox overlay,
confirmed all four edges of the existing cycle: normalization -> integral/rational
compact-support definition (stmt_deps) -> normalized lift (proof_deps) -> integral
coefficient comparison (stmt_deps) -> normalization (proof_deps). All seven new
helper/structure attachments remain absent from the shared DAG. The current
edge_fails implementation at tools/stage3_delivery.py:559--593 still requires
mutual base-graph reachability of the endpoints for its existing-cycle exception;
the newly introduced destinations cannot satisfy that condition.

The retained main theorem signature matches current shared sources after whitespace
normalization. The extracted instance/predicate declaration block matches after
removing comments and normalizing whitespace. The unit record and latest blueprint
unit text were read. The main and structures modules each have zero sorry tokens;
the four auxiliary theorem modules each have one. The current Q2 return file is
empty and rework.tsv has no item-specific row. No Lean or DAG dependency was
removed or changed, no tool or launcher script was modified or bypassed, and no
unchanged delivery was retried. Only this verification note was added. The packet
remains preserved for maintainer/tool-owner reconciliation of the inherited-cycle
gate failure.

Tenth-attempt verification (2026-10-25): the required initial deliver3.py run
completed with exit code 1. Server preflight again refused exactly the same five
category-(b) dependency edges and printed "PREFLIGHT FAILED, nothing pushed".
The four split-off theorem holes were explicitly a note, not a refusal. There
was no other failing preflight category.

A fresh traversal of the current shared DAG confirmed all four edges of the
inherited cycle through the integral/rational compact-support definition,
normalized lift, and integral coefficient comparison. The main theorem signature
still agrees with current shared sources after whitespace normalization. The
main and structures files have zero sorry tokens; each of the four auxiliary
files has one. No item-specific rework or return entry was found. The current
unit record was read and is unchanged.

Read the current edge_fails implementation in tools/stage3_delivery.py. Its
existing-cycle exception still requires mutual reachability in the base graph
for both endpoints of a new edge; a new auxiliary node cannot meet that test.
The five refused edges retain the actual canonical structures and proper parts
of the proof. No required dependency was removed, and no Lean, DAG, launcher or
project-tool file was changed or bypassed. The retained packet remains available
for the tool owner to reconcile this inherited-cycle refusal.


Eleventh-attempt verification (2026-10-25): the required initial deliver3.py
check exited 1 with the same five category-(b) dependency-cycle refusals and
"PREFLIGHT FAILED, nothing pushed". The four split-off holes were explicitly
a non-refusal note. No additional failing preflight category was reported.

Fresh traversal of the current shared DAG, without sandbox overlays, confirmed
the cycle normalization -> integral/rational compact-support definition
(stmt_deps) -> normalized lift (proof_deps) -> integral coefficient comparison
(stmt_deps) -> normalization (proof_deps). The current edge_fails implementation
at tools/stage3_delivery.py:559--593 still requires mutual base-graph reachability
for both endpoints of an added edge to qualify for its inherited-cycle exception.
The five new helper destinations cannot meet that condition.

The main theorem signature remains textually identical after whitespace
normalization. The extracted instance and predicate declarations also match
current source after comments and whitespace are removed. The main and
structures modules have zero sorry tokens; each of the four auxiliary theorem
modules has one. The unit record and latest blueprint unit were read. No
item-specific rework or return entry was found. No required dependency was
suppressed and no Lean, DAG, project-tool or launcher file was changed. Only
this verification note was added; the packet remains preserved for tool-owner
reconciliation of the inherited-cycle gate failure.

Current resumed-session verification (2026-10-25): the required initial deliver3.py
run exited 1, with exactly five category-(b) cycle refusals and no push. The four
split-off holes were explicitly a non-refusal note. A fresh read-only JSON traversal
confirmed the existing four-edge cycle through the compact-support definition,
normalized lift, and integral coefficient comparison. The theorem signature remains
unchanged after whitespace normalization; the main and structures modules have zero
holes, and each auxiliary theorem module has one. The current edge_fails function
still requires both new-edge endpoints to be mutually reachable in the base graph,
which the five new helper nodes cannot satisfy. tools/README.md reserves tool changes
to the maintainer. No Lean, DAG, launcher or project-tool files were changed, and no
required dependency was suppressed. The retained packet remains ready for tool-owner
reconciliation of the inherited-cycle gate failure.

Resumed-session check (2026-10-25, current dispatcher attempt): the required
initial deliver3.py invocation exited 1 at server preflight, reporting the same
five category-(b) added-edge cycle failures and "PREFLIGHT FAILED, nothing pushed".
The four split-off theorem holes were explicitly a note, not a refusal. No other
failing preflight category was reported.

A fresh parse of the current shared DAG confirmed the existing cycle:
normalization -> integral/rational compact-support definition (stmt_deps) ->
normalized lift (proof_deps) -> integral coefficient comparison (stmt_deps) ->
normalization (proof_deps). The five rejected helper destinations do not exist
in that base graph. tools/stage3_delivery.py edge_fails still exempts an added
edge only when both endpoints are mutually reachable in the base graph; these
new intermediate destinations cannot satisfy that test.

Compared the retained theorem signature with current shared source after whitespace
normalization: unchanged. Actual holes are zero in the main and structures modules
and one in each of the four auxiliary modules. Reviewed the four auxiliary
statements and the current unit record. No Lean or DAG file, required dependency,
launcher script or project tool was changed or bypassed. Only this verification
note was appended. The retained packet remains available for reconciliation of
the inherited-cycle gate failure by the tool owner.

## Second reading by Q2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
