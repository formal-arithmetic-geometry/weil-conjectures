## What changed

Replaced the first worker's fixed-degree restatement by the canonical-free
matrix-extension theorem `exists_local_free_stalk_map` in the new module
`Sheaf.AlgebraicGeometry.FiniteFreeStalkMapLocal`. The item's theorem now proves
both zero-term cases on the top open. For two free terms it conjugates the stalk
map by the chosen bases, invokes the canonical-free extension theorem, conjugates
the local map back, and checks the equation using comparison naturality and the
basis inverse identities. The original theorem signature is byte-for-byte unchanged.

Removed the redundant public import
`Mathlib.Algebra.Homology.Embedding.CochainComplex`: the retained public import of
`StalkRestrictionComplexIso` already supplies the complex declarations needed by
the signature. The new helper is a plain proof-only import. Updated the item's
node to record the actual reduction. No definition or existing statement changed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.Scheme.Modules.exists_local_degreewise_of_stalk_local`
(node `lem-pc-finite-free-stalk-degreewise-local`).

Hole added: `AlgebraicGeometry.Scheme.Modules.exists_local_free_stalk_map`
(node `lem-pc-finite-free-stalk-map-local`), in its own new module. Its entire
proof is `by sorry`, with the source and matrix argument in its docstring.
There are no other holes in the delivered modules. This is a decomposition:
one upper hole closed, one strictly narrower hole added, net zero. It does not
claim that the upper theorem is independent of sorryAx.

The submitted `exists_local_fixed_degree` and its proposed node were removed
before delivery: moving the degree quantifier did not prove a part of the
matrix argument. No data is chosen from an unproved existence theorem; the
remaining helper is used only inside a theorem proof.

## No longer needed

Removed import: `Mathlib.Algebra.Homology.Embedding.CochainComplex`.

Removed old direct proof-dependency edges:
`def-weil-pbc-free-module`, `def-weil-pbc-module-stalk`,
`def-pc-derived-pullback`. The free-sheaf and stalk ingredients remain beneath
the canonical-free helper, whose pullback is ordinary module pullback
`def-pc-module-pullback`. The retained direct dependency
`def-pc-stalk-restriction-complex-iso` supplies the comparison. No Sheaf or
WeilConjectures module is claimed to become unreachable.

The first worker's proposed `FiniteFreeStalkDegreewiseLocalFixed` module and
`lem-pc-finite-free-stalk-degreewise-local-fixed` node are not delivered.

## Where the brief, the DAG or earlier work was wrong

The first worker called introduction of the degree followed by application of
an otherwise identical holed theorem a proof. Its helper still took both
complexes, all degrees' hypotheses, and the entire family of maps. That was a
restatement, not a genuine reduction. The second reading replaced it by a
lemma solely about canonical finite free objects; the zero cases, changes of
basis, and comparison compatibility are now kernel-checked proofs in the item.
The original plan also listed derived pullback although the Lean statement
uses ordinary termwise module pullback.

## New nodes

`lem-pc-finite-free-stalk-map-local`, in
`dag/nodes/sec-picard-framework/lem-pc-finite-free-stalk-map-local.json`, states
only extension between the canonical finite free sheaves of ranks r and s.
It has no complexes, degree, family of maps, zero-term disjunctions or chosen
basis isomorphisms. Its proof is the finite matrix/germ argument from the
item's source, and its node records independent LeanFinder, Loogle and grep
searches, plus the recorded unavailable LeanSearch attempt. Change record: `coord/changes/FiniteFreeStalkDegreewiseLocal-imports.md`
documents removal of a public import; no existing statement or definition changed.

## Second reading by N3

1. Compared the delivered item with the repository by diff and compared the
   existing declaration's signature as bytes: identical. The only changes
   outside its proof are the explicitly reported import removal and plain
   helper import. There are no existing definitions to alter and no adapted
   modules. The original sole direct consumer,
   FiniteFreeStalkDegreewiseLift, compiled unchanged against the delivered
   overlay; its independent public embedding import preserves names for all
   738 transitive importers listed in the change record. Verdict: pass.
2. Compiled the two modules in import order using lcompile.py, without errors
   or warnings. Inspected every declaration for prohibited constructs and
   definition holes. The only sorry is the named, documented canonical-free
   helper. Explicit axiom probes of both theorems show only propext,
   Classical.choice, Quot.sound and the expected sorryAx. Verdict: valid
   decomposition with one remaining proof obligation, not a completed proof.
3. Checked the new statement against the matrix argument and the actual use
   in the reduction. Rank zero gives an empty matrix and the zero morphism;
   rank one gives one stalk coefficient represented by a section. Finite
   positive ranks require only finitely many representatives and an open
   intersection containing y. No boundedness or differential equation is
   smuggled in. Searched Mathlib independently for canonical-free stalk-map
   extension and pullbackObjFreeIso, and searched the project's Lean for
   local/stalk/free-map extension. The hits supply free-sheaf and germ tools,
   not the full extension equation. The new theorem is strictly the
   canonical-free matrix step; the remaining cases and basis transport are
   actually proved. Verdict: pass after replacing the submitted restatement.
4. Read downward from the item and checked its old proof plan. The repaired
   proof uses the zero-object and naturality lemmas directly from Mathlib,
   leaving only canonical-free extension open. Removed the unused embedding
   import and listed every removed old proof-dependency edge above. Read
   dag/units/sk-thm-picard-perfect.json: its realized fields are currently
   empty, and no unit statement or step was replaced. This is a reduction
   within the existing finite-matrix extension route. Verdict: pass.
5. Checked the modified original node's proof steps, dependency union and
   proof_origin against the Lean proof. Checked the new node's source,
   self-contained statement, dependencies, searches, creation and blueprint
   metadata, chapter/unit and verbatim Lean signature. The required LeanSearch
   attempt returned Internal Server Error and is recorded as unavailable. The new node has no
   copied review/landing metadata. Verdict: pass.

Second reading changed the invalid fixed-degree restatement into the
canonical-free matrix lemma, proved zero cases and basis conjugation, removed
the redundant import, repaired DAG proof metadata and corrected the report's
progress accounting.
