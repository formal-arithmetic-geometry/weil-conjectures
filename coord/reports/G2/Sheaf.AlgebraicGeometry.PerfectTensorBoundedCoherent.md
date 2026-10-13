## What changed

Proved `AlgebraicGeometry.Scheme.perfect_tensor_bounded_coherent` with its signature
and original docstring unchanged. The proof chooses a finite strictly perfect open
cover, obtains explicit local sum bounds, and descends vanishing and coherence.
The zero inserted in each endpoint set handles the empty cover without a
nonemptiness hypothesis.

Added `Sheaf.AlgebraicGeometry.StrictPerfectTensorLocalCohomology`, whose public
local calculation is proved. Its Lean proof transports the finite-free retractions
through the over-site equivalence, applies existing public flatness lemmas, invokes the
existing bounded-flat K-flat theorem, composes the derived restriction/tensor
comparisons, and identifies homology. Two proved private helpers establish the
ordinary total term's explicit vanishing and coherence of homology from coherent
terms via `ShortComplex.homologyIsoCokernelLift`.

Added `Sheaf.AlgebraicGeometry.FiniteRetractTensorComplexTerms` for the remaining
ordinary algebraic calculation: coherent terms of a total tensor with a bounded
finite-free-retract first complex. The second complex need not be bounded. This
statement contains no derived localization, perfect object, restriction, global
cover, or conclusion about homology. Updated the item's DAG proof and created
nodes for both public intermediate statements. All additions preserve the unit's
route, and no existing interface or other group's module is adapted.

Compilation of all three delivered modules succeeds. The local comparison needs
extra elaboration heartbeats for the two site equivalences and independently
chosen derived localization; it still compiles in roughly 30 seconds, below the
60-second single-file limit.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Scheme.perfect_tensor_bounded_coherent`
(node `lem-pc-perfect-tensor-bounded-coherent`).

Also proved the new public theorem
`AlgebraicGeometry.Scheme.strictPerfect_tensor_local_cohomology`
(node `lem-pc-strict-perfect-tensor-local-cohomology`) and both private helpers
`tensorComplex_isZero_X` and `coherent_homology_of_coherent_terms`. The duplicate
private `flat_retract` was removed in the repair; its call site now applies
`CategoryTheory.ObjectProperty.flat_coproduct` and
`CategoryTheory.ObjectProperty.flat_of_retract` from the existing imported library.

The delivery adds exactly one hole, and leaves no hole in the assigned module or
local comparison module:
`AlgebraicGeometry.Scheme.finiteRetract_tensorComplex_coherent_terms`
(node `lem-pc-finite-retract-tensor-complex-terms`). Its proof is exactly `by sorry`,
with its full source and natural-language argument in its docstring and DAG node.
This is a decomposition: one upper hole closed and one strictly smaller hole
added, so the direct hole-count net is zero. No claim of a sorry-free target is made.

Edge cases checked in the statements and arguments: empty scheme and empty
subcover, empty open, rank-zero retractions, zero complexes, reversed termwise
intervals, and unbounded N in the coherent-total-term statement. Reversed bounds
force P to be zero; the fixed total degree has at most one q for each surviving p.
There are no properness, relative-flatness, separatedness or nonzero-rank assumptions.

## No longer needed

The duplicate private `AlgebraicGeometry.Scheme.flat_retract` declaration is no
longer needed and has been deleted. No import of
`Sheaf.AlgebraicGeometry.LocalizedPullbackPerfectModel` is necessary: its private
helper is replaced by direct applications of the public general flatness lemmas
already imported from `WeilConjectures.CategoryTheory.Abelian.Flat.Basic`.

Removed the unused proof-only imports
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` from the new
`FiniteRetractTensorComplexTerms` module. They remain used in the local calculation;
this does not prune either module globally.

No original imports were removed; the four public imports still express the
unchanged signature. No original dependency node is globally pruned: the tensor
complex and derived tensor calculations remain needed through the proved local
comparison and its one remaining term-coherence lemma. Hence pruned modules: none.

The original top-level direct proof edges to
`def-pc-scheme-derived-tensor-structure`, `def-pc-tensor-complex-sheaves`,
`pqf-def-coherent`, and `def-pc-derived-category` are now routed through the local
comparison rather than used as if their definitions already supplied the argument.
They remain reachable; this is organization of dependencies, not pruning.

Removed a trial proof-only import of
`WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf` from the new local module;
it is needed in the assigned module for zero detection, but not locally.
No finite-free-refinement lemma, affine strict-model lemma, or Tor-amplitude
locality lemma was imported: the given finite-free retractions suffice directly.

## Where the brief, the DAG or earlier work was wrong

Repair of the returned delivery: the new local module duplicated the statement of
`AlgebraicGeometry.flat_retract` in `LocalizedPullbackPerfectModel`. That existing
helper is private, so importing that module does not expose a callable theorem.
Removed the duplicate declaration entirely. The transported-term calculation now
uses the already imported public `CategoryTheory.ObjectProperty.flat_coproduct`
and `CategoryTheory.ObjectProperty.flat_of_retract` directly, after installing
the required sheaf tensor instances. No declaration is renamed, no signature
changes, and no existing library module is adapted. The prior second reading
below records the pre-return delivery and predates this repair.

The original mathematical route is correct, but its definition-only dependencies
do not state the substantive local tensor calculation. That calculation has now
been assembled in Lean from existing comparison statements, with only coherence
of ordinary total terms split off. Kernel/cokernel closure is applied to the
incoming differential factored through cycles, rather than to an arbitrary
coherent quotient without a coherent source.

The Stacks TeX packet is absent from this clone's literature directory. I read
[Tag 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ) and
[Tag 01Y0](https://stacks.math.columbia.edu/tag/01Y0), and downloaded the relevant
TeX chapters into the sandbox scratchpad. The exact labels are
`perfect.tex: lemma-tensor-perfect` and
`coherent.tex: lemma-coherent-abelian-Noetherian`.
The flat/proper-support hypotheses in 0DJQ concern the subsequent pushforward,
not this local coherent-tensor calculation.

The blueprint ancestor lookup by `created.item` returns None for this recently
created module-linked item. The new nodes explicitly preserve the existing item's
recorded ancestor `lem-pc-rf-perfect-base-change` and its Noetherian local-tensor
step; no blueprint field of the existing item was changed.

Generic tools used from other units: coherence restriction/descent and coherent
kernel/cokernel/sum/isomorphism closure; bounded flat K-flatness and derived
open-restriction/tensor comparisons. They supply the same local calculation in
the fixed unit route. Please record these as tool uses if the unit checker requires
it. No unit or chapter statement or route was bypassed.

LeanSearch returned HTTP Internal Server Error and is recorded as unavailable.
LeanFinder and actual grep searches found no exact theorem. Blueprint-wide
searches found no duplicate; `def-weil-derived-tensor` is a tensor definition,
not the coherent-total-term calculation.

## New nodes

`lem-pc-strict-perfect-tensor-local-cohomology` records the proved calculation on
one specified open with one specified strict model and explicit sum endpoints.
Its module is `Sheaf.AlgebraicGeometry.StrictPerfectTensorLocalCohomology`.

`lem-pc-finite-retract-tensor-complex-terms` records the single remaining ordinary
term-coherence step, with a bounded first complex and an arbitrary termwise
coherent second complex. Its module is
`Sheaf.AlgebraicGeometry.FiniteRetractTensorComplexTerms`.
Both nodes have source labels, complete proofs in words, real search records,
and the original item's chapter and unit. There are no change records.

## Earlier second reading (a previous round; superseded)

Independent second reader, 2026-10-13; read all three Lean modules, all three
node records, the original module and node, and the unit's `realized` record.

1. **Interfaces: pass.** The diff of the existing module adds four plain proof
   imports and replaces only its theorem body. Its signature and original
   docstring are byte-for-byte unchanged. There are no adaptations or change
   records. The existing node changes only `proof`, `proof_deps`, and
   `proof_origin`. Both new node signatures match their Lean text exactly.
2. **Proofs and axioms: pass with the reported dependency holes.** Compiled all
   three modules through `lcompile.py --all`, again after import cleanup:
   4.0, 33.8, and 4.8 seconds; no errors or warnings. Scratch copies with
   `#print axioms` checked all three public theorems, all three private helpers,
   and both local monoidal instances. Only `propext`, `Classical.choice`,
   `Quot.sound`, and (where dependencies remain open) `sorryAx` occur. The flat
   retract and zero-total-term helpers and both local instances have no
   `sorryAx`. The coherent-homology helper depends on existing open coherence
   results. There is exactly one direct `sorry`, the reported public
   `finiteRetract_tensorComplex_coherent_terms`; no hollow definition or
   forbidden declaration is present. All Lean lines meet the 100-column limit.
3. **Split-off calculation: pass.** Read Stacks 0DJQ, `perfect.tex` label
   `lemma-tensor-perfect`, and 01Y0, `coherent.tex` label
   `lemma-coherent-abelian-Noetherian`, both online and in the scratchpad TeX.
   The total-term lemma isolates a strictly smaller ordinary algebraic step;
   it contains neither derived comparison nor homology nor a global cover.
   For fixed total degree, p ranges through the finite interval and q=i-p;
   zero summands can be discarded. Tensoring the splitting embeds each
   surviving summand as a retract of a finite sum of the coherent N terms.
   The retract is the kernel of identity minus the split idempotent, so
   coherent-kernel and finite-sum closure suffice. Rank zero, reversed bounds,
   zero complexes, and the empty scheme remain valid; no boundedness of N is
   required. The docstring and node give this complete argument and sources.
   Repeated searches using different wording: LeanFinder on bounded finite
   locally free direct summands and finite-type total terms; Loogle on
   `CochainComplex.mapBifunctor`; recorded Mathlib grep on coherent/projective
   tensors and retracts; and `rg` in both project roots. Results supply finite
   type definitions, totalization inclusions, and unrelated coherent-site
   lemmas, not this theorem. The scheme's `ZeroSupportFiniteScheme` tensor
   result has special support hypotheses and is not a replacement. Completing
   the remaining categorical coproduct/retract assembly is not a few-minute
   closure; the decomposition is retained without a net-progress claim.
4. **Top-down route and pruning: pass after cleanup.** The proof first extracts
   specified local strict models, uses compactness for a finite cover, takes
   extrema of endpoint sets containing zero, then applies local vanishing
   and coherence descent. The local proof actually composes the over-site,
   derived restriction, K-flat tensor, and homology comparisons; its cycles
   and boundary quotient use kernel/cokernel closure with coherent sources.
   Read those imported comparison statements and checked their hypotheses.
   No shorter matching declaration was found. Removed two unused proof-only
   imports from the term lemma (listed above). No existing dependency module
   is globally pruned. The four old direct proof edges now routed through the
   local theorem are all named above. `sk-thm-picard-semicon.json` has an empty
   `realized.statement` and an empty step realization already in the base;
   neither is changed. This below-unit local tensor reduction preserves the
   ancestor's Noetherian direct-image route and bypasses no realized step.
5. **DAG: pass.** Each node's `proof_deps` equals the union of its proof-step
   uses. Checked finite-cover/descent, local-model/comparison/homology, and
   coherent-total-term steps against the actual declarations or the remaining
   docstring argument. New nodes have source, search, creation, blueprint,
   chapter/unit, and verbatim Lean records required by the standing brief.
   The proof origins accurately distinguish the source route from its Lean
   assembly. Generic cross-unit coherence tools are reported above for the
   maintainer's tool-use accounting, without editing maintainer-owned fields.

Second reading changed only the removal of unused plain imports
`Sheaf.AlgebraicGeometry.CoherentKernelCokernelSum` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.TensorClosed` from
`FiniteRetractTensorComplexTerms`, and this report. No proof or signature
needed repair. One original hole is closed and one smaller hole is added:
this remains a decomposition with direct net zero, not a sorry-free proof.


## Second reading by G2

Independent second reader of the returned repair, 2026-10-13. Read the standing
stage-3 brief, stage document, AGENTS.md, lead review criteria, all three delivered
modules and nodes, the original module and node, the unit realization, the return,
and the comparison and coherence declarations used by the proof.

1. **Interfaces: pass.** Diffed the assigned module against the repository: only
   four plain proof imports and the original theorem body change. The existing
   signature and docstring are byte-for-byte unchanged. No target, definition,
   existing visibility, or other group's module changes; no change record is
   required. Checked all three node signatures against the actual Lean text.
   The existing node changes only proof, proof_deps and proof_origin.
2. **Proofs and axioms: pass with declared holes.** Independently compiled the
   delivered set through lcompile.py --all: term calculation 5.1 seconds, local
   comparison 35.0 seconds, assigned module 4.2 seconds; no errors or warnings.
   Compiled scratch copies with #print axioms for all three public theorems,
   both private helpers and both local monoidal instances. All use only propext,
   Classical.choice, Quot.sound and, where statements below remain open,
   sorryAx. The vanishing helper and both instances have no sorryAx.
   Exactly one direct sorry remains, the public named term-coherence theorem
   listed above with its docstring proof and node. No hollow definition,
   arbitrary witness defined from an unproved existence theorem, forbidden
   declaration or overlong Lean line occurs. Scratch probes were removed.
3. **Split-off statements: pass.** Independently read
   [Stacks 0DJQ](https://stacks.math.columbia.edu/tag/0DJQ) and
   [Stacks 01Y0](https://stacks.math.columbia.edu/tag/01Y0).
   The remaining statement is strictly the ordinary algebraic term calculation:
   bounded P leaves finitely many p, and q=i-p is determined even for unbounded N.
   Tensoring each finite-free retraction gives a retract of a finite sum of
   coherent N terms; the retract is the kernel of identity minus the splitting
   idempotent, and kernel, finite-sum and isomorphism closure finish.
   Checked rank zero, reversed bounds, zero complexes and empty schemes; none
   requires an extra hypothesis. The local comparison is actually proved,
   rather than a second hole restating the original result. Repeated searches
   with new wording through msearch.py LeanFinder, Loogle and grep, and rg in
   both library roots and the pinned Mathlib sheaf sources, found no matching
   theorem. Loogle's first fully qualified query was unknown; its subsequent
   mapBifunctor search found graded-object totalization machinery, not coherence.
   The remaining finite-coproduct/retract assembly is not a few-minute closure;
   retain this true decomposition without claiming positive hole-count progress.
4. **Route and pruning: pass.** Checked the finite subcover, extrema with zero
   inserted, vanishing descent and coherence descent from the top down. Read
   the open-restriction comparison, K-flat comparison, bounded-flat K-flatness
   and coherent closure statements and checked the proof's use of them.
   Coherent homology uses the cokernel of the incoming map into coherent cycles.
   The returned duplicate flat_retract is absent; the exact repaired call site
   uses ObjectProperty.flat_coproduct and ObjectProperty.flat_of_retract from
   the existing public upstream module. LocalizedPullbackPerfectModel's helper
   is private, so adding that import would not provide a callable replacement.
   Public imports supply signature definitions or total-tensor instances;
   added imports used only by proofs are plain. The four removed old direct
   proof edges are all listed under No longer needed and remain reachable
   through the local calculation. No original import or module is pruned.
   sk-thm-picard-semicon's realized statement and step lists are already empty
   in the repository; this delivery changes neither and bypasses no realized
   unit step. The Noetherian local-tensor route of the ancestor is retained.
5. **DAG: pass.** Every proof_deps list equals the union of the proof-step uses.
   The top-level finite-cover/descent steps, the local transport/flatness/
   comparison/vanishing/homology steps, and the remaining term-coherence
   argument agree with the Lean or the complete stated proof in words.
   Both new nodes have the required sources, search records, creation records,
   blueprint ancestry, chapter/unit and exact Lean signature records.
   The repaired local node correctly records the use of general flatness
   results and removal of the duplicate helper.

This second reading changed only this report, adding the independent review of
this returned repair and fresh verification evidence. No further proof, import,
statement or node repair was necessary. One original hole is closed and one
strictly smaller hole is added: decomposition, direct net zero; pruned modules none.
