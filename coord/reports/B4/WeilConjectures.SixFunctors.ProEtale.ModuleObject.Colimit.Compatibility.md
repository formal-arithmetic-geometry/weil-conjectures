## What changed

Implemented the scoped maintenance assignment
coord/repair-notes/B4-qlbar-continuity-assignment.md and its exact named entry in
coord/upstream-statement-exceptions.tsv. The proper-Qbar instance now explicitly
assumes preservation of coefficient-universe coproducts by the E-coefficient
derived direct image. Its complete proof applies the existing point basis and
proved scalar-unit copower/mate criterion. The canonical map and declaration
name are retained. The Qbar Shriek example has the corresponding hypothesis on
the chosen compactification's proper part and explicitly applies the corrected
Push instance and the unchanged formal Shriek theorem.

All unrelated source signatures, public imports, non-theorem bodies and the
entire finite-extension proof remain verbatim. The node carries its corrected
statement, exact Lean attachment, statement_change and actual proof dependencies.
Change record: coord/changes/B4-qbar-bounded-comparison-and-imports.md.

The independent retained QlbarDirectImageComparison proof and its node are
preserved under scratchpad/retained-bounded-companion for separate submission.
No consumer of this correction requires that additional delivery, and it is
not included or counted as landed work here. The earlier private all-family
criterion and finite-helper refactors are also preserved as scratch history.

## Proved and sorry left

Zero of one original assigned statements proved unchanged. The sole old hole,
AlgebraicGeometry.ProEtale.CondensedRing.isIso_derivedPushHom_padicSubfieldRingObjToPadicAlgCl_of_isProper
(node lem-sfb-qlbar-push-iso-proper), is removed by an authorized correction,
not counted as proof of its old properness-only assertion. The corrected
conditional instance is completely proved. Actual remaining hole count in the
assigned module: zero. Holes added: zero. Statements split off: zero.

The finite-extension theorem remains proved with its original proof. Existing
library dependencies may still include sorryAx; no transitive axiom-freedom or
ledger progress is claimed before the project's checks. The separate bounded
companion proof is retained but is outside this delivery's counts.

## No longer needed

No baseline import, declaration or module is removed or withdrawn. The added
private proof import CondensedQbarPointBasis is used directly. The earlier
packet's extra CoproductsOfCopowers import and private all-family criterion are
not needed by the actual repair and are retained only as scratch history.

The corrected node's direct proof does not use its old finite-stage dependencies
sk-prop-sfb-qlbar-colimit-x, lem-sfb-subfield-coefficient-map-comp or
lem-sfb-subfield-push-iso. These remain required elsewhere in the library and
unit; none is withdrawn. No global unreachability or module pruning is claimed.

The point basis, derived scalar-unit theorem, derived coproduct existence and
copower mate criterion are generic tools. They implement the coefficient
comparison while making the previously missing continuity an explicit premise;
no new continuity claim with sorry is introduced.

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED: the old node inferred ambient unbounded coproduct continuity
from properness alone, with no cited declaration in proof step 2 (uses: [],
elementary: null). B5's ringed counterexample analysis is evidence for independent
review, not a Lean-certified negation of the precise old internal-module
instance. The current maintenance authorization permits this scoped correction.

The original sk-prop-sfb-finite-extension-compatibility clause 3 claimed Qbar Push
for all proper maps and Qbar Shriek for all compactifiable maps on all unbounded
objects. Its corrected clause adds coproduct preservation by Rf_* over E, and
by the chosen compactification's Rg_* respectively. The original unit record
is preserved as source history. It needs maintainer reconciliation, as assigned
in the repair note; this delivery does not claim that old clause realized.
Flatness, Pull and finite-extension clause 2 stay intact. No target statement or
definition used by a target changes.

There are no structural DAG citers of lem-sfb-qlbar-push-iso-proper. All 50 direct
Lean importers were audited, including possible implicit coefficient-IsIso
consumers; the full table is in the change record. The four external direct
importers with coefficient push mentions use explicit bounded-below proofs or
still-stated bounded theorems. No external forced adaptation or further upstream
signature change is needed. CondensedQbarBaseChangeCompatibility already extracts
a lower bound and uses the independent bounded component theorem. The two-colimit
unit's bounded constructible use can retain that existing route.

The required initial delivery rejected the unchanged dispute packet with
FAILED: nothing is proved. The maintenance exception was then found and the
actual correction above was implemented. Diagnostic artifact generation exposed
an expensive concrete Push elaboration: prefixes through the finite helper
exported in 13.1 seconds, and through the finite-extension instance in 54.2
seconds; larger artifact checks hit 60 seconds. Those are diagnostic results,
not passed checks. No file or proof is split in the delivered source and no
limit or launcher tool is changed. The final delivery uses the ordinary
single-module compile and maintainer probe; their actual outcome is recorded
by deliver3.py and the project review/global-build process.

## Second reading by B4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
