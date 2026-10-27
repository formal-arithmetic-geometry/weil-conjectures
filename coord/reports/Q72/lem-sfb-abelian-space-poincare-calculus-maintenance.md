# Superseded Q72 stage-2 delivery closed

2026-10-24T03:18:16Z: maintenance disposition for `lem-sfb-abelian-space-poincare-calculus`.

The accepted stage-2 statement landed from NO's delivery `1efa38a93` in
`c7db4eab88`, with review `NT-stage2-cc-1efa38a93`. Its declaration remains
`AlgebraicGeometry.AlgebraicSpace.abelianSpace_poincare_calculus`.

The ordinary open return for Q72 head `a4653616cafdd197169e168b124be42b9f329522` contradicted its own
instruction to drop the duplicate and treat stage 2 as closed. Together with
Q72's outstanding claim, it caused repeated repair dispatches. The sandbox
had already removed the duplicate module and restored the accepted node.
Normal delivery correctly rejected a report-only packet with an unchanged node;
the wrapper's withdrawal path required no Lean record and could not represent
preservation of this accepted reviewed statement. This was a stale coordination
record, not an unfinished Lean statement or a mathematical failure.

Maintenance archived the exact returned commit at `refs/superseded/Q72/lem-sfb-abelian-space-poincare-calculus/a4653616cafdd197169e168b124be42b9f329522`, removed only
this return and Q72 claim, and recorded completion in the ledger and delivery
log. The delivery branch was already absent.
The accepted node, definition node, both Lean modules and review certificates
are unchanged. No Lean file changed, so no compile or lake build was run.
Backups of every changed record, including the deleted claim and an absence
marker for this new report, are in `/home/ubuntu/weil-maint-bak/Q72-poincare-calculus-20261024T031816Z`.

No further stage-2 worker or replacement delivery is needed. Refresh from
server `sheaf-dag`, preserve the accepted declaration and review, and do not
re-push the archived packet. A new concrete defect requires a fresh repair
instruction. Historical dispatcher notes and counters are not open work.

The protected review/landing-service owner should close the matching return,
claim and duplicate branch when recording stage-2 supersession, after checking
the accepted completion and exact obsolete head. It must not emit an ordinary
open repair return whose only action is to drop an already completed packet.
No protected tool or launcher code was edited by this repair.

## Preserved original supersession decision

## lem-sfb-abelian-space-poincare-calculus (2026-10-24 02:22 UTC, branch head a4653616caf)

L: independent stage-2 immutable head a4653616cafd: Superseded (A7 push after the merge; H4 second declaration). NO 1efa38a93 S2 FIX landed 10:05:37 (c7db4eab88): live lem-sfb-abelian-space-poincare-calculus lean = AlgebraicGeometry.AlgebraicSpace.abelianSpace_poincare_calculus with reviewed_lean NT-stage2-cc-1efa38a93; this review began 10:15:42. Q72 a4653616 is rebased on that landing (def node def-sfb-abelian-space-poincare-data byte-identical to live; item node differs only in lean.by/declaration/statement and carries NO's reviewed_lean). Its Lean file renames the theorem to AlgebraicGeometry.AlgebraicSpace.Poincare.exists_dual_poincare_calculus, makes S implicit, swaps the ComparisonCoherence/UniversalBaseChange conjuncts, changes imports (adds public Mathlib.AlgebraicGeometry.Scheme, replaces plain Mathlib Morphisms.Smooth by WeilConjectures SmoothFiber), uses public section instead of public noncomputable section, and condenses the six-step DAG proof docstring. Logically equivalent to the landed reviewed statement (same predicates from the landed AbelianSpacePoincareData, same universe u, no extra hypothesis), so nothing is gained. Landing would rename a reviewed declaration and leave NO's reviewed_lean certifying an unseen record. Correction: drop the branch; the item is closed at stage 2. Any desired change goes through a report/HUMAN.md note. No compile (no file changed).
