# NL flat ringed dg push-pull maintenance

The return of head 616b3f549c2c required an import of
Sheaf.CategoryTheory.SheafDgInjectivityTests. The live repository contained
neither that source nor its Lean node record or published object. Its only
source was unmerged Q125 delivery 4de8aa9c6fb. Current source-index inspection
confirmed no live owner. In nt_parallel2.commit, accepted candidates are added
to the in-memory declaration index before ordered_plans, DAG filtering and
transactional writing. A later return can therefore name a proposed module
which never lands. The return treated that provisional owner as available.

The shared IsHomotopicallyInjective definition is extracted verbatim from Q125
into SheafDgHomotopicalInjectivity, with its own definition node. NL and Q125
now cite the definition node. No theorem proof or statement was changed.
The NL return and both repair notes name the real source owner. Q125's pending
module must remove its local definition and publicly import the shared owner;
its remaining declarations and theorem are unchanged. Sandbox/route guidance
is maintained on the dispatcher machine.

Validation: the unchanged localization dependency compiled in 33.7 s and the
shared definition compiled in 6.1 s, each separately via tools/lean_file.sh
with a 60 s limit and a private maintenance group mirror. Follow-up consumer
compilation and DAG checks are recorded in the maintenance workspace REPORT.md.

The source-index/landing implementation is launcher-owned and was not changed.
It should check collisions against actual surviving writes, and a return must
not describe an uncommitted candidate as an already available import. This is
an ordering/correctness repair; no concurrency limit, throttle or pause is needed.
Every changed path has a .maintenance-NL-flat-dg-1792857681.bak sibling.

## Completed verification

The live shared module compiled separately in 2.4 s into the private maintenance
mirror. The NL FlatRingedDgPushpull consumer compiled cleanly in 9.0 s; the
Q125 SheafDgInjectivityTests consumer, with only its duplicate removed and shared
import added, compiled cleanly in 18.7 s. All calls used tools/lean_file.sh,
SHEAF_FILE_TIMEOUT=60, sequentially. No lake build ran and no published object
was changed. Prescribed scompile.py --source resolves the new live owner.

The normal deliver2.py NL lem-sfb-flat-ringed-dg-pushpull --no-push command
passed compilation and preflight at candidate 06c3d2ec528. This was a dry run;
normal dispatch/review/landing remains responsible for delivery of the item.
The before/after check_dag.py outputs differ only in node/reach counts: zero
added or removed findings. Existing cycles/reach/blueprint findings remain.
Both worker sandboxes and route notes were repaired, with .bak files.
Main theorem signatures and the node mathematical statements remain unchanged.

Primary repair commit: 9b5df59469c82a084684515f4e632bf5cfc015bf.
The next NL worker should retain the shared import and definition-node citation,
ignore historical missing-owner BLOCKED appendices, and deliver through the
normal tool. The pending Q125 branch 4de8aa9c6fb must be replaced by its repaired
sandbox before landing; its old local predicate would now collide with the
canonical shared definition. The Q125 route note and released repair record
state the exact extraction and unchanged theorem.
