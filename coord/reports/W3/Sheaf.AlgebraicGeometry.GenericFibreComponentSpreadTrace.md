## What changed

Corrected and proved `AlgebraicGeometry.generic_fibre_component_spread_trace` and
`AlgebraicGeometry.generic_fibre_component_spread_trace_reverse` in
`Sheaf.AlgebraicGeometry.GenericFibreComponentSpreadTrace`. The forward inclusion
now assumes `x ∈ A`; the reverse also assumes preconnectedness of the fibre trace.
Added the proof-only import `Mathlib.Topology.Connected.Clopen`. Mathlib supplies
clopen component containment and maximality of the component. Both proofs compile.
The two existing trace nodes now state the missing hypotheses and record these proofs.

Forced adaptation: `Sheaf.AlgebraicGeometry.GenericFibreComponentSpread` (unclaimed).
Its signature, visibility, docstring and imports stay identical; its invalid proof
is reopened at its existing named geometric theorem. No target changes.
Change record: coord/changes/generic-fibre-component-spread-trace.md.

## Proved and sorry left

Two corrected trace statements are proved without sorry dependencies:
`AlgebraicGeometry.generic_fibre_component_spread_trace`
(node `lem-sbc-generic-fibre-component-spread-trace`) and
`AlgebraicGeometry.generic_fibre_component_spread_trace_reverse`
(node `lem-sbc-generic-fibre-component-spread-trace-reverse`). The original statements
were false, so this is a statement repair, not a proof of those original statements.
Their two holes are removed only after explicitly recorded corrections.

One hole is reintroduced in the forced caller adaptation:
`AlgebraicGeometry.exists_open_generic_fibre_component_spread`
(node `lem-sbc-generic-fibre-component-spread`). Its signature and complete natural-language
source proof remain as before. This records the previously hidden geometric construction;
it is not a new node or a restatement of either trace theorem. No new module or new lemma
with sorry is added. Nominal holes removed: two; holes reopened: one. Treat the delivery
as correction of unsound intermediate interfaces, not proof of the geometric spreading.

## No longer needed

No existing imports removed. The trace proofs need only Mathlib; no geometric shrinking
node is needed for these corrected topological inclusions. The caller's imports are
retained because only forced lines may change. `GenericFibreComponentSpreadCore` remains
vacuous (`V = univ`, `A = univ`) and does not discharge the reopened geometric theorem;
its construction cannot establish the missing preconnectedness.
No unit-level route is bypassed (`sk-prop-normal-form` has no realized nodes).

## Where the brief, the DAG or earlier work was wrong

STATEMENT-DISPUTED (original forward): `A = ∅`, for any fibre point `x`.
The scratch theorem `empty_trace_counterexample` verifies this in Lean; it is
not part of the delivery. Its trace is
clopen, while `x` belongs to its component, so the requested inclusion fails.
STATEMENT-DISPUTED (original reverse): the finite morphism from two copies of `Spec k`
to `Spec k`, `A = P`, `V = T`. The trace is the whole disconnected fibre, not the
component through `x`. Merely requiring `x ∈ A` would still not fix this example.
The comments previously relied on A being the specially chosen component closure,
but the signatures quantified over an arbitrary clopen A. The existing caller selects
no such closure: its core theorem is proved by choosing the entire space.

Read Stacks https://stacks.math.columbia.edu/tag/055N, paragraphs on the closures of
the generic component and complement, and Tags 054Y and 054W. They concern specially
constructed closures, not arbitrary clopen subsets. The caller's geometric source
proof is retained for the next worker. Empty complements and single components satisfy
the repaired statements; the disconnected whole-fibre example is excluded by hconn.

## Forced adaptations

`Sheaf.AlgebraicGeometry.GenericFibreComponentSpread` is unclaimed. Its original
proof calls both trace theorems without the new hypotheses. Against the repaired
module, both calls return functions instead of the required subset proofs (the exact
compiler diagnostics are appended by deliver3.py). Only its proof body lines 50–55
are replaced with `by sorry`. The original compiler check must fail and the adapted
module must pass. No signature, import, docstring or visibility is changed.

## Second reading by W3

1. Compared both delivered Lean files with the repository using `diff -u`.
   The only changed existing signatures are the two trace inclusions, with the
   exact added hypotheses declared in the change record. These repair false
   intermediate statements; neither original statement is proved. The adapted
   caller has a byte-identical signature, imports, visibility and docstring;
   only its now-invalid proof is reopened. No definition or target is changed.
   Verdict: documented interface correction, not proof-only progress.
2. Compiled the entire delivered set locally through `lcompile.py --all`.
   Both files pass without errors or warnings. Scratch `#print axioms` checks
   show only `propext`, `Classical.choice` and `Quot.sound` for both trace lemmas.
   No forbidden declaration forms or data definitions occur. The sole delivered
   sorry is the whole proof of the existing named geometric spreading theorem,
   whose source proof and DAG node are present. The empty-trace counterexample
   also compiles. Verdict: the corrected statements have kernel-checked proofs.
3. No new statement or node is split off. The reopened geometric existence
   statement is strictly stronger than either trace inclusion and has its complete
   closure-and-shrinking proof in its original docstring. Read Stacks Tags 055N,
   054Y and 054W independently: the construction applies to the component and its
   complement and does not claim arbitrary clopen subsets are components.
   Checked empty traces, a single-point fibre, and a disconnected two-point fibre:
   added membership and preconnectedness exclude exactly the reported obstructions.
   New-wording leanfinder, loogle and grep searches locate the Mathlib topological
   lemmas already used, but no ready-made geometric spreading theorem; local
   searches find only the known core, trace and geometric caller declarations.
   Verdict: no unjustified split or arbitrary witness construction.
4. Read both proofs from their conclusions. The forward proof pulls back a clopen
   set to the fibre and uses component containment; the reverse uses preconnected
   maximality directly. No lower Sheaf sorry is used. The added Clopen import is
   proof-only; existing public imports provide signature names. No old trace
   proof dependency is pruned (both old lists are empty). The caller retains its
   imports under the forced-adaptation rule, rather than making extra edits.
   The unit sk-prop-normal-form has empty realized statement and step lists;
   no realized unit node is bypassed. Verdict: shortest existing topological
   route, no pruning claimed.
5. Compared both trace node records with the old versions: proof steps,
   proof_origin and empty proof_deps agree with the Lean. Both signature records
   include the declared added hypotheses, and each statement_change preserves
   the exact old statement and proof. There are no DAG citers of these trace
   nodes; the Lean caller is separately enumerated in the change record.
   The existing geometric caller node already records the source construction
   now left open, so its proof plan remains correct. Verdict: consistent records.

Second-reader changes: clarified the reverse node's conclusion to explicitly name
`g⁻¹({y}) ∩ A` instead of the ambiguous phrase "that trace", and added this review.
The Lean proofs required no repair. Counting: zero of the two original false
statements proved; two corrected statements proved; zero new split-off statements;
one existing geometric hole reopened. This is a statement repair, not a net proof
claim or a decomposition of a proved original statement.

## Forced adaptations

### Sheaf.AlgebraicGeometry.GenericFibreComponentSpread
Original against changed dependencies failed:
```
/tmp/forced-adaptation-1q3w6dur/lean/Sheaf/AlgebraicGeometry/GenericFibreComponentSpread.lean:54:4: error: Type mismatch
  generic_fibre_component_spread_trace_reverse g y x hx V A hV hy hcl
has type
  x ∈ A → _root_.IsPreconnected (⇑g ⁻¹' {y} ∩ A) → ⇑g ⁻¹' {y} ∩ A ⊆ connectedComponentIn (⇑g ⁻¹' {y}) x
but is expected to have type
  ⇑g ⁻¹' {y} ∩ A ⊆ connectedComponentIn (⇑g ⁻¹' {y}) x
/tmp/forced-adaptation-1q3w6dur/lean/Sheaf/AlgebraicGeometry/GenericFibreComponentSpread.lean:55:4: error: Type mismatch
  generic_fibre_component_spread_trace g y x hx V A hV hy hcl
has type
  x ∈ A → connectedComponentIn (⇑g ⁻¹' {y}) x ⊆ ⇑g ⁻¹' {y} ∩ A
but is expected to have type
  connectedComponentIn (⇑g ⁻¹' {y}) x ⊆ ⇑g ⁻¹' {y} ∩ A

(with the modules compiled into /tmp/forced-adaptation-1q3w6dur/.lbuild) [7.7 s]
```
Adapted module compiled in the delivered set. Explain the forced changed lines in the change record; CODEX verifies them.
