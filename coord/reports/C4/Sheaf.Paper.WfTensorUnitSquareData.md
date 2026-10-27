## What changed

Repair of returned head `9bb0dae0464` (reviewer `C-9bb0d`). Compared its retained
Lean sources with current `sheaf-dag` and compiled on the server against the
current published build. That build no longer registers
`WeilConjectures.scalarReductionSiteSmall` as an instance. The old prerequisite
adaptation therefore fails at its command-scoped exclusion with:
`WeilConjectures.scalarReductionSiteSmall does not have [instance] attribute`.
Removed the obsolete `WeilTensorProduct.lean` sandbox adaptation and its change
record from this packet. This is not a library withdrawal: the existing library
module stays in place and the assigned module imports its published version.
No `deleted.txt` is used.

The assigned module retains the reviewed repair: concrete local witnesses
`EssentiallySmall.{u + 1} X.ProEt := essentiallySmallSelf.{0} _` inside
`WeilConjectures.WfTensorUnitSquare.tensor` and
`WeilConjectures.WfTensorUnitSquare.beta`. Removed the file-wide overrides
disabling transparency and the redundant scoped settings enabling it on `beta`.
No declaration signature, mathematical construction, import, exported instance,
or DAG attachment changes. Proof irrelevance preserves the constructions.
The sole remaining change record is
`coord/changes/C4-wf-tensor-unit-square-universes.md`.

The previous delivery compiled the assigned module in 46.5 seconds and checked
its three unchanged direct consumers:
`WfCompletedConstantPullbackNormalization`,
`WfNormalizedKoszulFiberUnitTransport`, and `WfTensorPullbackCompletionUnitSquare`.
This retry compiled the retained repair on the server against the current
published prerequisite, without the obsolete sandbox adaptation: exit 0,
10.2 seconds, no errors or warnings. The delivery tool creates
its single commit on freshly fetched `sheaf-dag` and runs the server preflight.
No repository or launcher tool is modified.

## Proved and sorry left

The assigned definition repair starts with zero holes and adds zero holes.
No theorem hole is claimed closed or split off. There are no `sorry`
declarations in the delivered module. The original signed total tensor,
coefficient conjugation, Koszul tower, product, mapping fiber, and completion
unit are preserved.

## No longer needed

The prerequisite adaptation and its record
`coord/changes/C4-wf-tensor-representative-site-size.md` from returned head
`9bb0dae0464` are obsolete against the current published build and are omitted.
No library import, module, declaration, or dependency node is pruned or withdrawn.
The unit route and every existing DAG dependency remain unchanged.

## Where the brief, the DAG or earlier work was wrong

The returned landing rejected the reviewer-fix basename
`C4-wf-tensor-representative-site-size.md`. The landing reader maps a delivered
`coord/changes/<name>.md` to the flattened override alias `<name>.change.md`.
That prerequisite record is now obsolete and is absent from this packet.
For the sole retained record, the supported reviewer-fix alias is
`C4-wf-tensor-unit-square-universes.change.md`; accepting its complete delivered
contents requires no override.

The old prerequisite repair was necessary for the earlier published instance
environment but is invalid in the current one. Removing it is a substantive
repair of the returned packet rather than an unchanged re-push.

The original rework row correctly identified unresolved site-size universe
constraints in this zero-hole module. The local concrete site-smallness proofs
fix the ambiguity without changing its mathematical interface.
`tools/downstream.py` could not index the quarantined module during the initial
repair; the direct-import search over `lean/` and `quarantine/` found the three
consumers listed above and in the retained change record.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
