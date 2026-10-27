## What changed

Repaired the return of head cef61a06e36 concerning removal of the item after its
base f326929ff. I checked the current server records directly: A5 still holds
Sheaf.Paper.AdicReindexingTensor, its original source is present under lean/, its
quarantine copy is absent, and coord/rework.tsv has no row for it. The queue lists
its original one-hole proof obligation. The maintainer has therefore already
restored the archived source. This packet retains that declaration and its
original docstring, with precisely the same theorem signature, and supplies the
proof reduction on the current restored source. No deletion is requested.

The retained reduction has been repaired beyond a rebase: both split lemmas now
apply to one fixed scheme isomorphism, assume integral normalization only for
that map, and have complete docstrings and self-contained node statements. The
parent introduces the universally quantified spaces and inputs, specializes its
normalization hypothesis to that map, applies each component, and pairs the
results. The split modules now have module docstrings and keep the default
respectTransparency settings. The original three mathematical proof dependencies
are retained in the component nodes instead of being incorrectly reported pruned.
Actual msearch queries replace the unsupported search summaries in the old packet.

The modified modules are Sheaf.Paper.AdicReindexingTensor and its two new proof
modules Sheaf.Paper.AdicReindexingTensorCompatibility and
Sheaf.Paper.AdicReindexingUnitCompatibility. The two imports added to the existing
module are private proof imports. Its public import and every existing declaration
signature are preserved. No other existing Lean module is changed.

## Proved and sorry left

The original item has one sorry, in
WeilConjectures.AdicQbarRealization.normalized_reindexing_tensor. Its sandbox body
now compiles without a direct sorry. This is a decomposition, not a completed
mathematical proof: one upper hole is replaced by two strictly smaller holes.
No original mathematical obligation is completely discharged, and the net hole
change is one additional hole. There are zero direct holes in the item module.

The two remaining public theorem sorries are exactly:

- WeilConjectures.AdicQbarRealization.normalized_reindexing_tensor_compatibility,
  node lem-sf-adic-reindexing-tensor-compatibility. It asserts only the binary
  tensor square for a fixed scheme isomorphism.
- WeilConjectures.AdicQbarRealization.normalized_reindexing_unit_compatibility,
  node lem-sf-adic-reindexing-unit-compatibility. It asserts only the coefficient
  unit square for that fixed isomorphism and the specified unit witness.

These are the two obligations already present in the returned packet, now
localized and documented; this repair introduces no third split obligation.
Both remain exactly whole named theorem proofs with sorry. Their natural-language
proofs retain the quotient coaugmentation's zero shifted coordinate and the actual
common-stage comparison and unit witnesses. No data is chosen from a new theorem.

Validation: all three files compile individually in import order through
lcompile.py, without warnings, in 11.8 s, 6.3 s and 9.5 s respectively. The item
signature was compared verbatim with current main. The delivery tool runs the
axiom probes, import checks, preflight and any required consumer checks.

## No longer needed

None. No import, module or underlying mathematical dependency is pruned.
The parent now cites the two component nodes. The original dependencies
lem-fix-constructible-tensor-completion,
lem-pur-cochain-pullback-tensor-coherence and
lem-pur-derived-pullback-tensor-iso remain in their proof plans. In particular,
their absence from the immediate parent proof does not make them unnecessary.

## Where the brief, the DAG or earlier work was wrong

The return described the item while it was quarantined. The current server has
already restored its source; the older build-error file still records the bad
import of AdicRealizationFamilyData. The restored item and the current dependency
compile together. The existing A5 claim is still present, so no duplicate claim
or replacement empty module is needed.

The previous packet's new-node statements were only labels, its docstrings did
not contain full proof handoffs, its search summaries were unsupported, and its
report incorrectly claimed the underlying normalization dependencies were pruned.
Those deficiencies are corrected here. The earlier reported upper-hole closure
was a decomposition and is reported as such above.

The unit route and target statements are unchanged. The refinement is below the
existing node: the two independent conclusions are applied at each fixed map.
The construction plans handle zero tensor inputs and empty schemes by the same
section equations, and equal finite coefficient fields use the identity scalar
extension. The unit plan keeps C.unit_spec's particular chosen isomorphism and
the ordinary pullUnit built from the prescribed unitCochain, rather than selecting
new unit data. Bhatt--Scholze and HRS supply the realization and finite-stage
descent results; the precise map calculation is explicitly attributed to the
agent refinement inherited from the original node.

## New nodes

lem-sf-adic-reindexing-tensor-compatibility, in
Sheaf.Paper.AdicReindexingTensorCompatibility, records the tensor equation for one
fixed map and arbitrary inputs. Its proof plan keeps the common finite stage,
K-flat calculation, signed total tensor, entire quotient completion, and descent.

lem-sf-adic-reindexing-unit-compatibility, in
Sheaf.Paper.AdicReindexingUnitCompatibility, records the coefficient-unit equation
for one fixed map. Its proof plan fixes the unit using the prescribed unitors and
section normalization, then descends through integral realization and completion.

No change record for an existing shared interface is needed: only the item's
proof and its private proof imports change, alongside these new modules and nodes.

## Related modules compiled before delivery

No related module: no existing module's interface changes, or nothing imports it.

```json
{"capped": false, "direct": 0, "left_out": 0, "own": {"Sheaf.Paper.AdicReindexingTensor": "6135e6ffbf3326dd6fb96a1ddd6a2c424008f50e", "Sheaf.Paper.AdicReindexingTensorCompatibility": "a2ee848fb250f3674ec8226dc988e56a15a131e7", "Sheaf.Paper.AdicReindexingUnitCompatibility": "53389cc8a118f290cc769fbc1a065651923406ee"}, "results": {}, "time": "2026-10-28T02:12:14+0800", "transitive": 0, "version": 1}
```

## Second reading by A5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
