# NC duplicate stage-2 assignment retired: lem-sfb-ultrametric-orthogonal-extension

Resolved 2026-10-22T02:16:25Z under coord/.merge.lock.

NK already landed the stage-2 statement at 2026-10-21T22:48:25Z
(commit ec0b44f48a, reviewed batch 71f2cafdf44a492296742a34e27d9b84;
coord/ledger.md records the 22:48 reviewer PASS). The current node has
lean.by=NK and reviewed_lean.group=NK, result=pass. Stage 2 is complete;
the named theorem still has its reviewed sorry proof.

NC's stale claim and headed return kept the completed item dispatchable.
The 13th returned head 6504d1e1d80caa5c8864bd524f24062fbd8031d2 only changes
lean.by/lean.date, author credit and a redundant docstring sentence against
the accepted statement. Repeated failure counts are evidence, not a reason
to suppress dispatch. No mathematical repair or new NC delivery is needed.

Maintenance preserved the rejected head at refs/superseded/NC/lem-sfb-ultrametric-orthogonal-extension/6504d1e1d80caa5c8864bd524f24062fbd8031d2, retained the existing
refs/stage2-returned archive, closed only NC's stale claim with claim.py done,
and removed only the exact superseded return below from coord/returns/NC.md.
The delivery branch was already absent. This closes a duplicate assignment;
it is not a mathematical abandonment and does not transfer NK's credit.

Read-only reproduction before retirement: stage2_delivery.read_delivery
on the immutable rejected head against sheaf-dag returned fails=[],
nt_preflight2.graph_findings returned [], claim.node_finished(stage='2')
returned True, and queue_stage returned None. The saved-packet dry run
cecd53c4469 also passed preflight and per-file compilation in the worker log.

Protected tool follow-up for the launcher/landing owner: reject attribution-
or comment-only re-deliveries of an already reviewed stage-2 statement,
checking the current accepted node as well as the branch merge base.
Preserve an explicit path for substantive, independently reviewed statement
or dependency-interface corrections. Retirement-only returns need a terminal
record-maintenance outcome which archives the return/head and closes the
claim, instead of asking a worker to repair and push. No launcher, landing,
review-service, or preflight code was changed by this maintenance.

Next worker: do not re-push the retained NC packet or change the accepted
attribution. Use Padic.ultrametric_orthogonal_extension from
Sheaf.SixFunctors.UltrametricOrthogonalExtension. Any later stage-3 proof
assignment is separate.

Backups of all pre-existing edited files: /home/ubuntu/weil-newtargets-maint-bak/NC-lem-sfb-ultrametric-orthogonal-extension-20261022T021625Z/ (files end in .bak).
The maintenance note is new. Accepted source/record/report SHA256 values,
verified unchanged before and after retirement:

{
  "dag/nodes/sec-six-functors-basics/lem-sfb-ultrametric-orthogonal-extension.json": "1679b4f9a2b26b939268a1315dcca475d3d9fc18fe48a45004305164d1de66b6",
  "lean/Sheaf/SixFunctors/UltrametricOrthogonalExtension.lean": "a957fec1247178d479be6e17292984e3e51e79c2e9dcf52b84a262beb62f4a95",
  "coord/reports/NK/lem-sfb-ultrametric-orthogonal-extension.md": "8ae72a09997466204f482606eb3305ca22a697238fb0256fca43a7ac8bee8bd7"
}

Original retired return (historical evidence, not an open return):

## lem-sfb-ultrametric-orthogonal-extension (2026-10-22 01:56 UTC, branch head 6504d1e1d80)

L: independent stage-2 immutable head 6504d1e1d80c: A7/A6 (H2 credit): thirteenth NC head 6504d1e1d80c of lem-sfb-ultrametric-orthogonal-extension, which NK already landed (ledger 2026-10-21 22:48 stage-2 reviewer PASS; live lean.by=NK, reviewed_lean NK pass). Module sha a6eee1d3d477 and node sha 5fe09271f6d0 are identical to 12 returned NC heads; diff -rq vs returned 9ba3de0af4a6 differs only in blueprint-index.tsv and the report (more retry sections). Against side-live, only lean.by/lean.date NK->NC, the Authors line and one redundant minimizer docstring sentence differ; signature identical. Mathematics re-read and correct (coefficientExtensionAbsoluteValue, NNReal ultrametric norm, Finset.sup covers n=0, sInf minimality, Fin.snoc family, span = W + span{x}, independent universes, sorry only). Correction: NC must not re-push; the dispatcher/maintainer should retire NC's claim, keep NK's record, and fix the preflight gate that accepts already-merged credit-only packets.
