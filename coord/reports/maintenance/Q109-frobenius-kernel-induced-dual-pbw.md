# Q109 Frobenius-kernel induction: invalid reuse return

The stage-2 item lem-sfb-frobenius-kernel-induced-dual-pbw repeatedly failed
because the return of bed7ec2d12ba ordered the worker to import
Sheaf.AlgebraicGeometry.GroupScheme.FrobeniusKernelInductionData, remove four
definitions, and reuse their purported existing owners. That module was not
part of the landed library. The worker obeyed the return, producing a packet
that necessarily failed on the missing module before its own Lean elaborated.

Evidence obtained on 2026-10-25:

- coord/returns/Q109.md, entry committed by 4ed835e2c93, reports the four
  conflicts as a "current source index" refusal.
- All four named definitions occur in Q88's competing delivery
  957e28136c3051c8c4e847411de7659d93546d18, now retained only at
  refs/stale/deliver/Q88/lem-sfb-frobenius-kernel-induced-dual-pbw.
  That commit is not an ancestor of sheaf-dag; its module and owning node are
  absent from the current source tree. This was never a usable published import.
- The Q88 preparation survives in
  local/stage2/parallel/0e0c8841d2b959ccf1c110fcd4cf039f5cba2a35a192a256645626c6704eda1a.json.
  Its reviewer explicitly notes that parallel Q109 is also unlanded and only
  one implementation may land.
- Q109's original independent review at
  local/stage2/reviews/cc__Q109__lem-sfb-frobenius-kernel-induced-dual-pbw__bed7ec2d12ba/review.md
  says PASS and found no live name clash. Its subsequent return was mechanical.
- The current parallel source-index pickle contains neither that Q88 module
  nor an owner for induced, push, relations or sigma in this namespace.
- The repair retained the nonexistent import for many retries; the final
  pre-maintenance attempt spent 403.4 s and 2410.1 s including service waits
  on compilation and dry run, respectively, and confirmed the missing module.

The batch code explains how this false return can arise. In
tools/nt_parallel2.py:commit, each candidate is added to the in-memory source
index before ordered_plans filters conflicting writes. Later stale-head,
live-conflict and changed-input guards can also reject candidates. Consequently
a later candidate can see an earlier unlanded same-item alternative as an
existing module and receive a return demanding an impossible import. The exact
guard that excluded Q88 is not recorded by this maintenance audit; the unlanded
owner and invalid return are directly verified.

This is a landing-tool issue. Per the maintenance instruction, neither that
landing tool nor the review service was changed. The required follow-up is to
check conflicts against actual landed sources plus only candidates that will
survive the transaction. Competing same-item candidates should yield a retry,
not an instruction to import one another. Remove rejected candidates from the
temporary index and rebuild conflict checks when the survivor set changes.
Add a regression where one candidate contributes a declaration, loses its
same-item write conflict or stale-head guard, and another must still land.
No throttle, admission limit, pause, or concurrency cap is involved.

Repair performed:

- Restored the Q109 sandbox construction module and its definition-node record
  byte for byte from bed7ec2d12ba, including all four bodies and ownership entries.
  The theorem source and its mathematical statement were unchanged.
- Appended the maintenance correction to the sandbox report. A resumed worker
  subsequently condensed the obsolete blocker history while retaining this
  correction and successfully redelivered.
- Replaced the invalid live return body with the correction and added a
  persistent launcher route note. Existing changed files have backups with
  suffix .maint-Q109-1792861614.bak. New files have .bak absence markers.

Validation:

- tools/lean_file.sh, 60 s per invocation, private source tree and group artifacts:
  AffineGroupDistributionCalculus 4.3 s, FrobeniusInductionConstructions 8.0 s,
  BorelRootProductCoordinates 5.7 s, FrobeniusKernelInducedDualPBW 17.5 s.
  No errors or warnings. No lake build.
- stage2_delivery.read_delivery on the restored packet, nt_preflight2.graph_findings
  on the current DAG, and import_prune_check on each module against current
  server sources all passed at fba9cb296f5298b6d8df16b4408117ce826268b2.
- The concurrently resumed worker completed two normal dry runs (8537038bfcc,
  11017159274) and successfully delivered aeac121c7be. It picked up the restored
  sandbox without a process restart or pipeline pause.

Next worker: use the current node/delivery status, preserve the restored Q109
implementation, and proceed through ordinary review and landing. The old
FrobeniusKernelInductionData reuse instruction is withdrawn. This is a repair
of the pipeline record and packet, not a new mathematical result or a landing
approval.
