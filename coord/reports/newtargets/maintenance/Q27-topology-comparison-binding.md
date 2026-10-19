# Q27 topology-comparison binding maintenance, 2026-10-18

The repeated stage-1 repair of `lem-trf-comparison-equalizer-class-killing`
was blocked by inherited maintainer-owned metadata, not its mathematical proof.
The returned head is `4f87997f7b`. Both live and side nodes bound the general
Stacks 0EZD equalizer-killing lemma and its 0EZE parent to `sk-i-curve-zero`,
whose statement is Frobenius local-term vanishing. No existing unit stated
this general comparison theorem. Stage-1 delivery correctly overlays only
split-owned fields and cannot install this repair. A side-only change would
be overwritten by the committed live snapshot.

Installed `dag/units/sk-lem-trf-topology-comparison.json` first in the live DAG.
Its statement is copied exactly from the reviewed refinement-vanishing node
(0EZF). Its sixteen steps are copied verbatim from the existing reviewed
0EZE induction (thirteen) and 0EZF induction assembly (three); no mathematical
argument is newly written. Realization identifies those existing carriers
and the four 0EZA–0EZD supporting comparison nodes. Its four prerequisite
units supply the existing general sheaf-cohomology and derived-functor tools.

Rebound these six records, changing only `unit`:

- lem-trf-comparison-equalizer-class-killing
- lem-trf-comparison-induction-step
- lem-trf-comparison-next-degree-image
- lem-trf-comparison-truncated-cohomology
- lem-trf-comparison-truncated-direct-images
- lem-trf-refined-topology-comparison-vanishing

In `lem-trf-ph-big-etale-torsion-acyclicity`, accepted its existing use of
`lem-trf-refined-topology-comparison-vanishing` in `tool_uses`: the caller
checks the five general comparison hypotheses and applies the vanishing
theorem as a black box. Its specialization/normal-cone route is unchanged.
All statements, proofs, dependency edges, Lean records, historical
`blueprint.from`/`via`/`created` ancestry, and the Frobenius unit are preserved.
No chapter or source blueprint is edited. The new record binds the already
reviewed general-purpose tool route; it does not replace the local-term proof.

Before writes, the production `units.check` was compared in memory before
and after this exact metadata overlay: 1811 pre-existing live findings in
each case, zero new findings. Every field except the six unit fields and
the one accepted-tool list was checked equal. Stacks `situation-compare`,
`lemma-make-class-zero-general`, `lemma-induction-step-V-C-general`, and the
initial induction paragraph of `lemma-V-C-all-n-general` were read directly.
No Lean file changed; no compiler or global build is needed for metadata.

Next worker: refresh the base from current newtargets-dag. Keep the retained
eight-step proof, citations and logged searches. The normal delivery overlay
will preserve the corrected authoritative unit even if a retained sandbox
still has the old unit. Update the report to say the metadata blocker was
resolved by this maintenance. Run the normal no-push check, then submit via
the ordinary delivery and independent review. Keep the original return open
until that review accepts the new delivery; a metadata repair is not acceptance
of the old returned head. Do not relabel blueprint ancestry or invent a new
mathematical node. Keep historical dispatcher counts; no scheduling or process
change is part of this repair.

Every changed file has a sibling backup ending
`.maint-Q27-topology-comparison-1792272996.bak` (empty before new files).
Server commits use Bin Wu <844524296@qq.com> under SHEAF_LEAD=L-only and the
repository merge lock. The same binding must be refreshed in weil-newtargets
under its merge lock so normal live sync keeps it persistent.

Authoritative live maintenance commit: `94687fb585fba54dba7a2d9b9c788625f36fa45a`. This side refresh preserves side-owned split and Lean fields.
