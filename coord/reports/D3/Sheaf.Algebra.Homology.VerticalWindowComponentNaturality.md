## What changed

Proved `HomologicalComplex₂.verticalWindow_component_naturality` in its original module,
with its existing signature, docstring, definitions and public import unchanged. The proof
uses single-complex morphism extensionality and composes the upper-truncation cycles,
homology projection, inverse lower-truncation homology, and extension homology naturality
squares. A private equality-transport lemma matches the cast in `verticalWindowDegreeIso`.
The existing node's proof now records this route; its original proof dependencies remain.

## Proved and sorry left

Closed one original hole: `HomologicalComplex₂.verticalWindow_component_naturality`
(node `lem-sp-vertical-window-component-naturality`). No holes remain in the delivered
module and no holes are added elsewhere. This is a proof, not a decomposition.

The first worker's proposed `HomologicalComplex₂.verticalWindow_degree_naturality` hole
was closed during the second reading and the calculation was inlined in the original
proof. Its proposed module and node are omitted from the final delivery. All private
helper proofs are complete.

## No longer needed

No original library import, proof-dependency node, or module is pruned. Both original
proof dependencies, `lem-sp-vertical-window-component-iso` and
`lem-sp-vertical-window-degree-iso`, are used. The proposed proof-only import of
`Sheaf.Algebra.Homology.VerticalWindowDegreeNaturality`, its new module, and its new node
`lem-sp-vertical-window-degree-naturality` are removed from this sandbox delivery.
The unchanged sandbox copy of `VerticalWindowComponentIso` is omitted. The truncation
helpers that were previously unused now participate in the complete proof.

## Where the brief, the DAG or earlier work was wrong

The earlier report described a decomposition and claimed its truncation helpers were
unused. That description is superseded: the second reading completed the missing cast
calculation and uses those helpers. Direct simplification fails because the degree
isomorphism transports across the equality `q + 1 - 1 = q`; equality induction proves
naturality of that transport without changing the isomorphism's definition.

The cited blueprint source is not present in this machine's literature checkout. Review
therefore uses the unchanged node statement, the actual definitions and Mathlib sources,
and the unit record. No source or target statement correction is proposed.

## Second reading by D3

1. Compared every initial sandbox module with its repository version. The additional
   `VerticalWindowComponentIso` copy was byte-identical and is omitted. The final delivery
   changes only the original module's proof and private proof helpers. A literal substring
   comparison confirms that the existing theorem signature and docstring are byte for byte
   unchanged. No public imports, definitions, hypotheses or conclusions change. Verdict: pass.
2. Compiled the initial set and the repaired original module through `lcompile.py`.
   The repaired module compiles without errors or warnings and contains no `sorry`,
   forbidden declarations, or hollow definitions. An appended scratch `#print axioms`
   checks `HomologicalComplex₂.verticalWindow_component_naturality`; its only axioms are
   `propext`, `Classical.choice`, and `Quot.sound`. Verdict: pass.
3. Read the proposed degree-naturality statement and node. It was the degree-q substep;
   its proof was completed and inlined, so no split-off statement or new node is delivered.
   Searched Mathlib with `msearch.py` grep for truncation comparison naturality and
   single-complex extensionality, LeanFinder for extension/truncation homology comparison
   naturality, and Loogle for `HomologicalComplex.extendHomologyIso_hom_naturality`.
   Also searched both library roots. The relevant Mathlib naturality lemmas and
   `to_single_hom_ext` are used directly. The private lower-boundary helper in
   `LowerTruncationStepSES` is unavailable externally and only addresses integer cochain
   truncation; the generic private helper here also handles the opposite embedding.
   Checked q = 0 (the predecessor is the integer -1), identity and zero maps, and zero
   complexes: no positivity or nonvanishing assumption is introduced. Verdict: pass.
4. The proof proceeds from the target down through single-complex extensionality, then
   the four canonical naturality squares. Its only import is the original public import
   needed by the theorem statement. Both old proof dependencies are retained and used;
   the report lists the discarded proposed module separately from baseline pruning.
   Read `dag/units/sk-prop-av-pqf-finite.json`: its `realized` lists are empty and are not
   changed by this delivery. The canonical comparison route in the existing node is
   preserved, with no replacement of a unit step. Verdict: pass.
5. Compared the existing node against the final Lean proof. Its statement and Lean
   signature record remain unchanged; `proof` describes extensionality, the four squares
   and equality transport, and `proof_deps` names the two original construction nodes
   that the proof actually uses. `proof_origin` retains the original cited canonical
   comparison source. No new-node field requirements remain applicable. Verdict: pass.

Changes made during second reading: completed the degree calculation using equality
transport; inlined it into the original theorem; made the formerly unused helpers part
of the proof; removed the proposed split-off module/node/import and the unchanged extra
module; corrected the existing node's proof route and this report. No statement changes.
