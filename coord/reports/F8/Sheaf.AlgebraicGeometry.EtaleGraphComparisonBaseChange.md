## What changed

The seven-clause statement of
`AlgebraicGeometry.Etale.etaleGraphComparisonBaseChange` is unchanged, including all
universes, hypotheses, orientations, and the two quasi-compact refinement clauses.
Its proof now assembles independence, open normalization, identity, cocycle, forward
and inverse arbitrary base change, common-refinement normalization, and the named
common-refinement iso by explicit cancellation of the specified graph isomorphisms.
The generic private inverse-exchange, quotient-exchange and paired-equation lemmas
cancel only the comparison isomorphisms. They also keep the derived-functor expressions
out of generic categorical elaboration; local irreducibility of the underlying functor
constructors prevents unnecessary unfolding. No proper exchange is inverted.

Moved the existing presentation structures, functors, graph maps, normalizations and
successive exchange definitions verbatim into
`Sheaf.AlgebraicGeometry.EtaleGraphPresentation`, publicly re-exported by the assigned
module. Added the explicit `ofCompactificationBaseChange` constructor from the two
existing compactification pullback squares and an identity square. All definition data
remains explicit; the graph-model theorem supplies only Prop properness witnesses.

The existing pairwise-product normalization already implies independence, because its
lambda formula is independent of the auxiliary compactification. Its module previously
imported the assigned module only for the presentation definitions. Redirected that
public import to the shared definition module, retaining every existing signature and
map. Rebased this file onto the current W3 proof, retaining its geometry, projection,
helper and main normalization proofs verbatim. Only its public definition import changes.
The proof now uses the existing proper-ambient and open-shrink lemmas. Redirected their
public imports to the same shared definition module. Both statements and postponed proofs
are unchanged. All three adapted modules are unclaimed in the current claim records.

Repair of the return at 7d33c49c33c: removed every copied private declaration
from `EtaleGraphDiagonalNormalization` (436 lines reduced to 65). Lean's module
`import all` exposes the existing private proofs for use in proof bodies. The diagonal
now reuses `unbounded_refinement_comparison` and `unboundedFormalism` directly from
`UnboundedEtaleCompactSupportComparisons`, then applies the generic identity law.
No declaration is copied or renamed, and the owning module needs no modification.
The proof keeps arbitrary schemes; it adds no Noetherian or finite-type hypotheses.

Checked the latest blueprint's compact-support/smooth-base-change coherence route,
Stacks Tags 0F7B--0F7F, the actual graph formula and the refinement unit/base-change API.
The unit route is retained. Edge cases include empty X, repeated presentations, zero
coefficients, identity squares, non-quasi-compact supporting opens and arbitrary
unbounded complexes. No target statement or source-library declaration changes.

Repair of the return at ae4dc602260: the latest pairwise proof imports the two
new elementary-move modules, which still imported the bundled base-change theorem.
The previous packet missed both resulting cycles. Rebased the pairwise module and its
node on current main, preserving its complete proof. Redirected all three definition
imports to `EtaleGraphPresentation`, and redirected the three nodes' definition
references. No theorem is used circularly. A merged-source audit traversed 8,526 modules
in the assigned module's import closure and found no cycle. Each adapted Lean file is
byte-identical to current main except for its one public import line. All eight packet modules compiled in import order without errors or warnings;
individual compiler times ranged from 41.1 to 45.7 seconds. The assigned module compiled
in 45.7 seconds. Its theorem signature is byte-identical to current main, all Lean
lines meet the 100-character limit, and proof dependencies match the union of step uses.

Change record: `coord/changes/etale-graph-presentation-interface.md`.

## Proved and sorry left

The assigned module initially had one hole. Its named theorem
`AlgebraicGeometry.Etale.etaleGraphComparisonBaseChange` now has a complete assembly
proof from named dependencies. This closes that syntactic hole by decomposition;
it is not claimed as an independent proof of the two new geometric facts below.

The current shared baseline already proves
`EtaleGraphPresentation.PairwiseProduct.b_projections` and `.geometry` (B6).
Those proofs and the current W3 pairwise normalization proof are preserved verbatim
and count as zero new closures in this repair.

Proved the new theorem
`AlgebraicGeometry.Etale.etaleGraphComparison_diagonal`, node
`lem-pur-etale-graph-diagonal-normalization`, with no local hole. It depends on the
single-refinement normalization below. Its identity-refinement calculation directly
reuses existing private proofs through `import all`, adding no declaration or hole.

Added exactly two postponed declarations, each in its own new module:

- `AlgebraicGeometry.Etale.etaleGraphFromOpen_baseChange`, node
  `lem-pur-etale-graph-from-open-base-change`: compatibility for one normalized graph
  map E, before taking the two-map quotient C. Its complete factorwise cube/pasting
  argument is in its docstring and node. This is strictly one part of the original
  base-change argument; the main module proves composition, inverse compatibility,
  and both C equations itself.
- `AlgebraicGeometry.Etale.etaleGraphFromOpen_refinement`, node
  `lem-pur-etale-graph-refinement-normalization`: one Cartesian proper refinement,
  with no quasi-compactness assumption or common-refinement choice. Its graph-transport
  and canonical unit/open-base-change/compositor argument is in its docstring and
  node. The main module combines two such comparisons and proves the inf formula.

Two pre-existing holes remain unchanged in the import-adapted elementary-move modules:

- `AlgebraicGeometry.Etale.etaleGraphComparisonFromOpen_openShrink`, node
  `lem-pur-etale-graph-comparison-open-shrink`.
- `AlgebraicGeometry.Etale.etaleGraphComparisonFromOpen_properAmbient`, node
  `lem-pur-etale-graph-comparison-proper-ambient`.

Current-baseline packet counts: one existing hole closed in the assigned module;
two holes added; four holes remain in the eight delivered Lean files, including the
two unchanged elementary-move theorems. The pairwise normalization has zero holes on
current main. This is a decomposition with net minus one, not an independent proof or
a claimed net hole reduction. Previously landed geometry and pairwise proofs are not
counted again. There is no `sorry` in a definition or private declaration.

## No longer needed

The proposed new triangle-law module was removed from the sandbox before delivery:
independence is already a consequence of the existing pairwise-product normalization.
It was never a library module or landed DAG node and needs no withdrawal.

Removed all copied private helpers and their three implementation imports from
`EtaleGraphDiagonalNormalization`: `Compactification`, `CompConjugate`, and
`RefinementLowerShriekBaseChange`. Their existing owning implementations remain intact;
the diagonal now reuses those existing private proofs through `import all`. No existing
library module is pruned by this repair.

Removed the assigned module's direct proof imports
`Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal` and
`Mathlib.CategoryTheory.Adjunction.Mates`. The assembly proof needs only the three
named normalization/base-change results and the existing pairwise normalization.
Replaced the public import of `EtaleGraphComparisonBaseChange` in the pairwise,
open-shrink and proper-ambient modules with `EtaleGraphPresentation`: each needs the
specified maps and definitions, and none uses the seven-clause theorem.
Removed unused proof imports from both new postponed modules after their statements
were checked; their docstrings and DAG nodes retain the actual proof dependencies
for the future geometric proofs.

The original direct proof dependencies are now needed, where applicable, by the
corresponding geometric sublemmas rather than by the assembly. The main node's old
off-unit tool approvals are withdrawn because the assembly does not directly use
them; no claim is made that those mathematical tools disappear from the overall
closure. The shared definition module retains all original public definition imports.
Every original proof dependency still occurs in the geometric sublemmas or the
pairwise normalization node. No existing mathematical module or node is withdrawn
or pruned.

## Where the brief, the DAG or earlier work was wrong

The original proof plan is mathematically consistent but the Lean interface bundled
its definitions with the full coherence theorem. The already stated pairwise-product
normalization needed only the definitions, so its import created an avoidable cycle
for using its stronger independence consequence. The shared definition module removes
that cycle without changing any existing map or theorem signature. The pairwise, open-shrink and proper-ambient nodes' references are corrected to the
definition node, with their current DAG citers audited; their mathematical statements
are unchanged.

The returned packet wrongly copied private lemmas that the library already states.
Their privacy does not authorize duplication. The earlier claim that private proofs
cannot be reused from another module was wrong: `import all` is the supported Lean
module mechanism, already used elsewhere in this library. The repair imports and reuses
them, preserving every declaration and leaving the owning module untouched.

Single-file server compiles sometimes could not find the unpublished graph-model
object while reading an already compiled sandbox dependency. Batch `lcompile.py --all`
compiles the unpublished dependencies in its private overlay; no library or launcher
script was changed or bypassed.

A broader DAG audit found an existing dependency cycle in the unchanged shared
baseline: `lemma-weil-pbc-derived-exchange-replacement` ->
`lem-weil-pbc-derived-exchange-termwise` ->
`lem-weil-pbc-derived-exchange-unbounded-transport` ->
`lem-weil-pbc-derived-exchange-bounded-comparison` -> the first node. The edges
are already present in the repository; this packet changes none of these nodes or
their Lean modules. Reported here for the maintainer to reconcile.

## New nodes

`def-pur-etale-graph-presentation-maps` attaches the verbatim moved presentation data
and specified maps, plus the explicit compactification base-change record. It adds
no proof hole and retains the graph model's actual product/intersection construction.

`lem-pur-etale-graph-diagonal-normalization` states the single self-comparison
B(c,c)=N(c) inverse. Its proof uses the one-refinement graph normalization and the
existing private unbounded refinement normalization and formalism identity law.
Its node now records that reuse rather than a copied construction. No new
identity-refinement node or public API theorem is added by the repair.

`lem-pur-etale-graph-from-open-base-change` is the factorwise arbitrary-base-change
compatibility of one normalized graph map E=N;B. It contains one named postponed
proof, with the source, all pasting steps, and all used dependency nodes recorded.

`lem-pur-etale-graph-refinement-normalization` identifies one graph comparison with
one specified Cartesian refinement comparison, restoring its target identity direct
image. It contains one named postponed proof, including the proper ambient graph
transport and the precise unit/open-base-change/K-injective normalization.

The original node's statement is unchanged and its proof now describes the actual
Lean assembly. The new nodes inherit the original chapter, unit and null blueprint
ancestor; the current blueprint was searched and no duplicate was found. All three
required kinds of Mathlib searches are recorded. The change record is
`coord/changes/etale-graph-presentation-interface.md`.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
