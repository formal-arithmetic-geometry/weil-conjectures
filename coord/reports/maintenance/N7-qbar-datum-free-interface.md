# N7 maintenance: arbitrary-base-field coefficient readiness

Cause: `def-weil-integral-rational-qbar-compact-support` was dispatched at stage 2 with all `stmt_deps` carrying Lean records,
although `def-weil-algebraically-closed-coefficients` still exposes only a `FiniteFieldDatum`-parameterized common-stage
category. `SfAlgebraicallyClosedCoefficients.transition` passes D.p and hl into the rational
scalar functor, so the recorded category structure does not expose the general interface
the consumer needs. The current main blueprint compact-support definition (order 1849)
allows an arbitrary field K₀ and l invertible in it. The coefficient source (order 1821,
master 1462) is stated with the global datum. Its finite-field interface is valid as a
specialization; no relation between Y and that finite field is asserted. The missing
general construction/identification, rather than a finite-field assumption on Y, is the
defect. Source wrappers work. The worker's bottom-up brief correctly forbids repairing
another owning DAG node inside the consumer delivery.

History: Q22 maintenance reopened the intrinsic coefficient chain after an integral
predicate migration. Those intrinsic interfaces landed; Q37's common-stage interface
landed in side commit `998caa1e69` (batch 76bf40eacedf478bbd4de27dfbda9cfc, reported 37 s
compile). It repaired the old predicate, but kept the datum parameters. Recent N7 logs
repeated the same blocker, including attempts 1792173187 through 1792176663. The failure
counter is retained and is never a reason to stop dispatching.

Change: preserve all Lean files and source statements. Archive the current full `lean`
and `reviewed_lean` records in a new `lean_invalidation`, retaining the complete earlier
invalidation in its history. Remove only the active readiness records of the owner in
the authoritative shared DAG and the side project, committed under each merge lock.
This reopens the actual missing interface through normal stage 2 and makes the existing
bottom-up gate withhold the consumer. Repair notes and route notes give a concrete
acceptance condition; the existing preflight invalidated-alias guard rejects an unchanged
`existing: true` attachment. This is a metadata repair, not a new mathematics delivery.

Required interface: Expose the intrinsic common-stage coefficient construction for arbitrary schemes with only a prime l and an algebraic closure Ω of Padic l; preserve independent scheme/closure universes. Keep existing finite-field declarations for callers, and supply the canonical specialization/identification with them, including scalar transitions, normalized associators, Hom transports, shifts and distinguished triangles. Retain actual pairs (E,K), the Hom colimit, and no Karoubi completion. A bare sigma carrier, an arbitrary auxiliary FiniteFieldDatum, or adding D to the consumer is not the missing interface.

Owning-node instructions: Repair only this owning node through the normal bottom-up stage-2 delivery. The global datum in its source does not impose a structure morphism on Y. The underlying completed integral extension and intrinsic integral/rational categories already work for arbitrary schemes; inspect the proof-only p/hl parameters rather than assuming a field structure on the geometric base. Generalize/reuse those canonical constructions and give their specialization, without restating other DAG nodes or weakening any statement. The main finite-field signature by itself must not be reattached as the completed repair. The worker report and independent review must check a category-valued interface with no D binder, its real category/shift/triangle instances, and the literal output pair (E, Rf_! K_E) used over an arbitrary base field. Compile each changed Lean file singly through the prescribed 60-second wrapper, then run the normal no-push delivery check.

No other coefficient owner is invalidated: the intrinsic integral/rational categories
and the p-parameterized scalar-extension/composition interfaces already supply the
general underlying data. If their internals need a helper, use a helper in the owning
module with its proper specification, keeping the bottom-up ownership rule.

Validation: reproduce admission before withdrawal; run the production Dag.stage2 and
nt_stage2.eligible after withdrawal to check the owner opens and compact support does
not. Replay an in-memory completion of the owner to check compact support opens again;
this replay is queue testing only, never a Lean certification. Compare both committed
owner records; verify all fields except lean/reviewed_lean/lean_invalidation are unchanged.
Run the invalidated-binding preflight check against the old record and a candidate with
a newly published declaration. No Lean file changed, so no Lean compilation or global
build is needed for this repair. Eventual owner and consumer deliveries must compile
every changed Lean file separately with the 60-second wrapper.

Original files have sibling backups ending `.maint-N7-qbar-interface-1792176826.bak`. New notes have empty preimage
backups. Commit hashes, actual validation results and dispatcher observation are recorded
in the maintenance working directory's REPORT.md. Do not reset counters, add retry limits,
park/abandon the item, kill a worker, or restore an archived record to force readiness.
