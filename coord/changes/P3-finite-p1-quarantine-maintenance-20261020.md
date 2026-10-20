# P3 finite projective-line quarantine maintenance (2026-10-20)

## Cause

Item: Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals, returned head
 e8875da621cf7e5044b9957559a89b905bfa6d2e, dispatcher key ending @e8875da62.
The returned packet withdrew the module because it had no current Lean consumers.
That is insufficient: lem-per-ordinary-smooth-orientation and
 det-sp-tower-p1-adjunction still cite lem-sp-tower-p1-arbitrary-base-integrals.
The latter has the quarantined attachment Sheaf.Paper.SmoothPurityTowerP1Adjunction.
Neither parent route was replaced by the withdrawal packet. A parent with an
unfinished proof need not import the lemma yet. The earlier S9/J1 withdrawals
and stage-2 restatements already demonstrate this cycle.

Upstream sync then quarantined the active item at 2026-10-20T10:47:43Z.
coord/rework.tsv preserves its source and reports imports of
Sheaf.AlgebraicGeometry.HigherDirectImageRawDiagram. The old return still asked
for a rebase of an active file. The dispatcher repair lane replayed the withdrawal
packet without the rework context appended to ordinary claimed rework jobs.
deliver3.py lines 106-116 correctly rejects a nonexistent active deletion path
and also requires an item source or accepted deletion; repeated retries cannot
resolve those incompatible inputs. This is a stale assignment and brief problem,
not a mathematical failure or provider failure.

## Changes

The active launcher brief briefs/batch1/stage3-worker.md now says to inspect
coord/rework.tsv before copying an absent source, preserve quarantined sources,
attachments and dependencies, and use the restoration assignment. Step 8d now
requires checking the DAG parents and unit route, including quarantined parents;
zero Lean importers alone does not justify withdrawal. The equivalent clarification
is in coord/brief-stage3.md. The deployed launcher patch is retained beside this
record as P3-finite-p1-quarantine-worker-brief3.patch.

Launcher brief before SHA-256: 095b1e3bc19aa4832e32171df8b6377ccf73517a3db2e96c29ef85857a83fc74
Launcher brief after SHA-256: f27f3b3ea250fbb52e3dca73468480738549011dc48ca7dc5d3a57bc3855824a
Launcher backup: /home/ubuntu/weil-launcher-all/briefs/batch1/stage3-worker.md.P3-finite-p1-1792502160.bak
Server brief backup: coord/brief-stage3.md.P3-finite-p1-1792502160.bak

During this investigation the independent rework sweep committed e2c5229cd6:
it removed the obsolete P3 return, released the obsolete claim and archived the
old delivery at refs/superseded/P3/Sheaf.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals/
e8875da621cf7e5044b9957559a89b905bfa6d2e (one ref, with no newline).
This maintenance did not rerun that sweep or introduce scheduling controls.
The superseded packet remains available as evidence, rather than as a live repair.
No launcher-owned dispatcher or landing tool was edited.

## Validation and handoff

Confirmed the archived source exists, the active source is absent, the node still
has its stage-2 Lean attachment, the two DAG parent edges remain, the returned
branch is archived, and the P3 return and claim are gone. The module has 46
transitive quarantined prerequisites in the current rework records; restoration
belongs to that dependency repair workflow. No Lean source changed and no Lean
compilation was needed for this brief-only repair.

The next assigned worker must start from the current rework/source state. Do not
replay the sandbox's deleted.txt, lean:null node, or unused-withdrawal change record
as if the old return were still active. Back those files up before refreshing a
retained sandbox. Restore the real source through a rework assignment and retain
its statement and mathematical node; ordinary proof work can then use the stated
prerequisites. Absence of present importers is not a replacement argument.

## Launcher-owner follow-up

The dispatcher repair path should reconcile pre-sync returns with current rework
records and give a genuine rework repair its restoration brief, as the ordinary
claimed-item path does. This is an owner change to dispatch_all.py and was not made
here. Do not relax the deleted.txt existence check merely to replay this packet:
that would revive the erroneous withdrawal/re-statement cycle. If a future reviewer
explicitly approves withdrawing an already-quarantined item, the owner must define
an atomic protocol for its archive, rework row and attachment before changing the
delivery/landing gates; those tools were outside this maintenance's edit scope.
