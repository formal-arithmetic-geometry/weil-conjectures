## What changed

Replaced the sorry in `AlgebraicGeometry.formalComparison_completed_affine_adjunction_model`
with a complete Lean proof, preserving its signature and docstring. The proof explicitly takes
the canonical base change to the completion of each affine chart, establishes Noetherianity
and completeness of that ring, transports the formal comparison, and applies complete-base
algebraization. It composes the two resulting section isomorphisms and pastes their squares
using the proved private helper `compose_comparison_squares`.

Added three modules with their DAG nodes. `CompletedAffineComplementBaseChange` is proved
entirely from Mathlib: support/zero-locus identities give the inverse-image complement,
and two pullback-associativity isomorphisms transfer the original isomorphism. The other
two modules state the separate flat transport and complete-base algebraization steps.
Neither merely renames the original theorem: transport has no algebraic source or lifted
isomorphism, while algebraization works on a complete affine ring and has no original affine
chart, completion base change, exceptional ideal or open-complement assertion.

All added imports in the assigned module are proof imports. Existing public imports remain.
The second reading narrowed the new complement module to IdealSheaf.Basic and removed
the redundant public IdealSheaf.Functorial import from the new transport module.
No definitions, existing signatures, target statements, or held modules were changed. The
scoped transparency options avoid expensive unfolding of the formal-system category during
elaboration. The scoped unused-variable linter option preserves the existing unused
existential binder `hD` without renaming it. No heartbeat increase is needed.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.formalComparison_completed_affine_adjunction_model`
(node `lem-weil-pbc-formal-comparison-completed-affine-adjunction-model`).
There is no sorry left in the assigned module.

Also proved `AlgebraicGeometry.completedAffine_complement_base_change`
(node `lem-weil-pbc-completed-affine-complement-base-change`), with no imported Sheaf proof
holes, and the private categorical square-pasting helper.

Added exactly two named public theorem holes, each the whole proof `:= by sorry`:

- `AlgebraicGeometry.formalComparison_completed_affine_transport`, node
  `lem-weil-pbc-formal-comparison-completed-affine-transport`.
- `AlgebraicGeometry.formalComparison_complete_base_algebraization`, node
  `lem-weil-pbc-formal-comparison-complete-base-algebraization`.

This is a decomposition: one upper hole closed, two lower holes added, net holes closed
minus added equals -1 before any other closure changes. It is not a sorry-free proof of the
original theorem. All four delivered Lean modules compile together without warnings.

## No longer needed

No existing imports were removed and no existing dependency module is globally pruned.
The assigned node's direct proof dependencies are now the two new comparison steps, the
proved complement step, and completion Noetherianity. Its former flat base-change, affine
formal-module, formal-system pullback, full-faithfulness and formal-functions dependencies
are retained under the appropriate new step, not claimed as pruned.

Former direct proof dependencies no longer used directly by the assigned proof:

- `def-pc-fibre-product`.
- `def-weil-pbc-coherent-formal-module`.
- `lem-pc-coherent-hi`.
- `lem-weil-pbc-adic-completion-mod-power`.
- `lem-weil-pbc-coherent-formal-modules-affine`.
- `lem-weil-pbc-flat-base-change-map-sections`.
- `lem-weil-pbc-flat-base-change-resolution-iso`.
- `lem-weil-pbc-formal-completion-fully-faithful-proper`.
- `lem-weil-pbc-formal-systems-pullback`.
- `lem-weil-pbc-noetherian-completion-flat`.
- `lem-weil-pbc-theorem-formal-functions`.

These are removed direct DAG edges, not globally pruned modules. Their mathematical
roles remain in the two unfinished steps (or in their signatures); proper coherent
pushforward is explicitly recorded in the transport node. The unfinished steps currently
import their statement prerequisites only. Their DAG proof dependencies are plans for
filling those holes, not claims of existing Lean proof references or retained import edges.

The complement argument uses only Mathlib and ideal/fibre-product definitions; it needs
neither flatness nor properness nor Noetherianity. The formal transport needs no exceptional
ideal K or isomorphism over its complement. The complete-base algebraization needs neither
K nor the original completion map or affine chart. Their new signatures omit these genuinely
unused hypotheses, while the assigned signature stays unchanged.

## Where the brief, the DAG or earlier work was wrong

The original module imports only statement prerequisites, not the proof-dependency modules
named by the DAG. Several of the planned dependencies provide existence/equivalence
interfaces without the canonical completed-base section square needed here. The two new
statements make those separate gluing steps explicit; no existing statement was disputed.

`blueprint_refs.py ancestor` returns None for this item because its `created.item` is a
module name. The new records inherit the existing node's `blueprint.from.node` and prepend
the assigned node to its `via`, preserving the recorded source lineage rather than changing
any unit or chapter. Blueprint searches for 088B, formal pullback, affine completion and
completed affine comparison returned no imported blueprint duplicate.

The existing complete-affine section-isomorphism lifting and affine-morphism-realization
modules were also read. They do not supply the proper-source formal pullback lift and its
unit comparison required by the complete-base step. No cycle through the parent comparison
or its restriction-isomorphism theorem is introduced.

Edge cases were checked in the mathematical statements: empty U/zero R gives zero section
systems and the empty base change; J=0 gives constant systems; a unit J gives zero systems;
K=0 gives the empty complement and K=1 the whole complement. Neither new hole excludes
these cases. The geometry proof itself covers them uniformly, without extra assumptions.
LeanSearch was unavailable; the actual failed queries and successful LeanFinder/Loogle and
Mathlib source searches are recorded in searches.jsonl and the new nodes.

## New nodes

`lem-weil-pbc-formal-comparison-completed-affine-transport`, module
`Sheaf.AlgebraicGeometry.FormalComparisonCompletedAffineTransport`: restrict and flatly base
change the actual formal data to the canonical completed chart, preserving the two comparison
equations and giving natural scalar-restricted section-limit isomorphisms. Still sorry.

`lem-weil-pbc-formal-comparison-complete-base-algebraization`, module
`Sheaf.AlgebraicGeometry.FormalComparisonCompleteBaseAlgebraization`: algebraize the source
over a complete affine base, lift the formal pullback isomorphism on the proper source and
identify the limit map with the algebraic adjunction map. Still sorry.

`lem-weil-pbc-completed-affine-complement-base-change`, module
`Sheaf.AlgebraicGeometry.CompletedAffineComplementBaseChange`: identify the complement of
the extended ideal and transfer the given open isomorphism by pullback associativity. Proved.

Each node has a self-contained statement, source, complete proof steps, actual searches and
its Lean signature. No change record is needed because no existing interface changes.

## Second reading by S3

1. Compared every delivered module with the repository. Only the assigned module already
   exists; its original theorem signature and docstring are byte-for-byte unchanged.
   Its added helper is private and proved. The other three modules are new. No existing
   definition, visibility, target or public import changed. Verdict: pass.
2. Compiled all four modules through lcompile.py in import order, without warnings.
   Scanned for forbidden declarations and proof escapes: none. Exactly the two reported
   named theorems have whole-proof sorry; there are no new definitions or hollow data.
   A scratch module printed axioms: the complement lemma has only propext,
   Classical.choice and Quot.sound; the main theorem and the two open steps additionally
   use sorryAx, as reported. Verdict: valid reduction, not a fully closed target proof.
3. Read both split statements and their complete proof docstrings against Stacks
   [088B](https://stacks.math.columbia.edu/tag/088B),
   [087W](https://stacks.math.columbia.edu/tag/087W) and
   [0883](https://stacks.math.columbia.edu/tag/0883). Checked zero ring/empty chart,
   zero and unit adic ideal, zero coherent objects, and zero/unit exceptional ideal.
   Complete-base algebraization uses completeness and properness for full faithfulness;
   transport constructs actual pullbacks and preserves the canonical comparison.
   No arbitrary witness is selected inside a definition. The two steps have different
   hypotheses and conclusions and strictly separate transport from algebraization;
   neither restates the item. Repeated LeanFinder searches using finite modules on
   infinitesimal neighborhoods and flat direct-image/unit naturality, Loogle on mapIso,
   and Mathlib/library rg searches. Existing affine realization and completed-affine
   coherent-isomorphism lifting do not lift the given isomorphism on the proper source.
   Neither remaining hole has a few-minute closure by an existing exact lemma.
   Verdict: both statements accepted as sourced, strictly simpler open steps.
4. Read the proof top down: canonical completed base and proper pullback, transport,
   complete-base algebraization, proved complement base change, categorical square
   pasting. No shorter exact route was found. Narrowed the complement import from
   IdealSheaf.Functorial to IdealSheaf.Basic and removed the redundant public
   Functorial import in transport; the new statements still elaborate. Expanded
   No longer needed to enumerate every removed direct proof-dependency edge and
   distinguish those edges from global import pruning. Read sk-thm-p1 realized: the
   assigned node is below its realized unit steps, and its parent comparison chain is
   retained. No unit record or unit route changed. Verdict: pass after import/report repair.
5. Matched all four Lean signatures to their node lean.statement, checked proof-step
   uses against proof_deps, sources and blueprint lineage, and read the parent-node
   changes against its repository version. Added the missing proper coherent direct
   image dependency lem-pc-coherent-hi to transport's coherence step and dependency
   union. The two open nodes record mathematical proof plans; they do not claim that
   their still-sorried Lean proofs reference those declarations. Verdict: pass after
   the dependency correction.

Second-reading changes: narrowed/removal of two redundant imports, explicit proper
coherent-pushforward dependency in the transport node, exhaustive removed-direct-edge
reporting, and this independent review. No proof body or signature was rewritten.
