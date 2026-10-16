## What changed

Replaced the proof of
`AlgebraicGeometry.SchemeSplitAttachment.exists_attached_split_structure`
in `Sheaf.Paper.FiniteSplitReplacementAttachmentStructure` without changing its statement.
The proof follows all three steps of the existing node. Private, fully proved helpers
package degreewise nondegenerate and matching data, transport the splitting cofans,
construct the new matching map using the boundary's unique universal property,
and prove exact equality after restriction. All old data are retained. The new
nondegenerate object is explicitly V with the coproduct inclusion; no arbitrary
existence witness supplies geometric data.

Added the proof-only import `Mathlib.AlgebraicGeometry.LimitsOver` to obtain the
coproduct instances for the category of etale schemes over X.

## Proved and sorry left

Closed the sole hole:
`AlgebraicGeometry.SchemeSplitAttachment.exists_attached_split_structure`
(node `lem-weil-pbc-finite-split-replacement-attachment-structure`).
No holes added or split off. No sorry remains in the delivered module.

## No longer needed

Removed the redundant direct proof imports
`Sheaf.Paper.FiniteSplitReplacementStage` and
`WeilConjectures.AlgebraicGeometry.FiniteSplitEtaleHypercover`.
Their declarations remain used and available through the existing public import
of `Sheaf.Paper.FiniteSplitReplacementAttachmentConstruction`.
No DAG node or module is pruned; all three original proof dependencies remain necessary.

## Where the brief, the DAG or earlier work was wrong

No mathematical or statement defect found. The existing statement and all three
proof steps are used unchanged. No new nodes, signature changes, or forced adaptations.

The initial dry run treated an anonymous local coproduct instance as an added
public declaration. Replaced it with the private theorem `attachmentCoproducts`
with instance registrations confined to the construction proofs. Helper parameters
are explicit, preserving the original file-level commands; the coproduct construction
is unchanged.

## Second reading by E2

1. **Unchanged interface: pass.** Read the entire delivered module and compared it
with the repository version. A byte comparison of the existing theorem's complete
signature, up to `:= by`, passes. Its docstring is unchanged. All added declarations
are private; the public import is unchanged. No other Lean module, definition used
by a target, or existing statement is changed, so no change record is required.

2. **Proof and axioms: pass.** `lcompile.py` compiled the delivered file without
errors or warnings. A scratch copy prints axioms for the public theorem and all
19 proof/construction helpers: every result uses only `propext`, `Classical.choice`,
and `Quot.sound`, with no `sorryAx`. A complete token scan finds no `sorry`,
`axiom`, `unsafe`, `opaque`, `extern`, or `implemented_by`. In particular the
nondegenerate scheme is explicitly V, the lower objects and maps are retained,
and the new matching map comes from Q's unique universal property. No data is
chosen from an undetermined existence theorem.

3. **Split statements and shorter routes: pass.** No statements or holes are
split off. Read the private reductions and their uses: they prove coproduct
transport, degreewise extension, matching universality, and strict restriction
separately, rather than hiding the target under another name. Independent
`leanfinder` and `loogle` searches used coproduct/cocone transport terminology;
the returned reindexing theorem is already used. Repository searches found no
existing attachment theorem that replaces this argument. Checked the degree-zero
boundary case: lower matching cones are empty when their index is zero, and both
the old-label reindexing and unique top identity label remain valid for n = 0.
Surjectivity is proved directly from b through the new inclusion, so it also
handles empty schemes without any nonemptiness assumption.

4. **Route and pruning: pass.** The proof carries out the node's three steps:
transport old splitting data and separate the new identity label, construct the
top matching map, and retain finite presentations with exact restriction.
The cone equations use functoriality of the already constructed simplicial
object (whose construction establishes the attachment operator laws). All three
old `proof_deps` are still used. The two redundant direct imports listed under
`## No longer needed` are removed; the new Mathlib import is proof-only and supplies
the coproduct instances. No node or module is pruned. Inspected
`dag/units/sk-prop-h2.json`: its `realized` record and its route are unchanged;
this proof stays below the unit level.

5. **DAG and documentation: pass.** Read the existing node
`lem-weil-pbc-finite-split-replacement-attachment-structure` and its three dependency
declarations. Its statement, `proof`, `proof_deps`, and `proof_origin` agree with
the Lean argument; no new node is needed. There is no relevant change record in
the shared repository. The report names the sole closed hole and records zero
added holes, so this is a proof, not a decomposition.

Second reading changed only this report by adding the required audit. No Lean or
DAG repair was necessary. Validation: clean single-file compile and clean axiom
probes in `scratchpad/lean/Sheaf/Paper/AttachmentStructureAudit.lean`.
