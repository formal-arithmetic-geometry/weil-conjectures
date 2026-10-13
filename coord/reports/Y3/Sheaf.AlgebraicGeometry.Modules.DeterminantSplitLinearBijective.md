## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.determinant_split_linear_maps_locally_bijective`
with a compiling reduction to the new common-chart comparison theorem. The existing
statement and visibility are unchanged. Added one proof-only import,
`Sheaf.AlgebraicGeometry.Modules.DeterminantSplitChartComparison`, and proof-only Mathlib
imports for exterior bases, product bases and tensor bases.

The main module proves the algebraic argument directly. Extend lifts only of the quotient
basis vectors by `Basis.constr`. This gives a linear section of g. Under the supplied
splitting, `f.coprod t` is a triangular isomorphism. Its image of the product basis is a
middle-module basis. The given wedge formula sends the tensor of the two top basis wedges
to the top wedge of this basis. These are singleton bases, so the linear map is their
basis equivalence. Transport through the sheafification and tensor comparisons and prove
bijectivity of the original map. No arbitrary data is chosen from an unproved existence
statement in a definition: the new comparison is used only inside a theorem proof.

Updated the original node's proof route and dependencies, and added the new node and module.
Both modules compiled together through lcompile.py, with no warnings. The algebra argument
includes rank zero, zero rings, and empty opens; no nontriviality or scalar cancellation
is used. The algebraic map equality needs only the given formula at the two basis tuples.

## Proved and sorry left

Closed the original hole in
`AlgebraicGeometry.Scheme.Modules.determinant_split_linear_maps_locally_bijective`
(node `lem-sc-split-determinant-linear-bijective`).

Added one remaining hole:
`AlgebraicGeometry.Scheme.Modules.determinant_split_chart_comparison`
(node `new-y3-determinant-split-chart-comparison`, module
`Sheaf.AlgebraicGeometry.Modules.DeterminantSplitChartComparison`). Its entire proof is
`by sorry`, with its source and full argument in its docstring and node. This is a
**decomposition**, not an axiom-free proof: one upper hole is closed and one strictly
smaller chart-comparison hole is added. The new statement has no lift function l, no
linear determinant map d and no determinant wedge formula; those are handled in the
proved algebraic argument of the main module.

No sorry remains in the main module. All private helpers are proved.

## No longer needed

The new route does not need `new-j1-exterior-sheaf-rank-wedge-zero`
(module `Sheaf.AlgebraicGeometry.Modules.ExteriorSheafRankWedgeZero`) or
`lem-sc-exterior-top-direct-sum`
(module `Sheaf.LinearAlgebra.ExteriorTopDirectSum`). Their proof imports were absent in the
provided original module; none was added. Both dependencies are removed from the original
node's proof_deps. Pruning here is from this item's proof, not a claim that these modules
are unused elsewhere in the targets' closure.

`lem-sc-exterior-sheaf-local-free-comparison` remains needed by the proof plan of the new
chart lemma. It is moved down to that node, not pruned. Its theorem already proves the
exterior-unit comparisons once common free frames are available.

No original public imports were removed: they support the existing statement. No unused
proof imports remain in the delivered main module. Exploratory helpers for transporting a
splitting through overEquiv and for the tensor comparison are omitted from the delivery.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan's lift-independence expansion is unnecessary
for proving bijectivity: one may choose the middle basis using precisely the given lifts of
the quotient basis vectors. The original top-direct-sum comparison is likewise unnecessary;
the top exterior and tensor singleton bases suffice.

The first planned step requires more than exteriorSheaf_local_free_comparison supplies:
that theorem takes a free frame and gives exterior-unit bijectivity, but does not assemble
a common frame, evaluate the splitting, or prove the tensor section comparison. Those
interfaces are now stated explicitly in the new chart theorem. Attempts to close this
interface ran into the transport of biproduct splitting compatibility through overEquiv;
the delivered module contains no partial private proof or hidden sorry.

The literature/blueprint source files are not installed in this read-only clone; the source
and first-step argument were read from the supplied DAG node. The new proof_origin is marked
as an agent expansion of that step, using the inspected proved library APIs. The unit
sk-thm-picard-rr and its realized route are unchanged. A whole-blueprint search for
"exterior comparison" and searches of the existing module and node trees found no duplicate
of the complete chart statement. LeanSearch returned an internal server error, recorded as
unavailable; LeanFinder and source searches found component APIs rather than a full match.

## New nodes

`new-y3-determinant-split-chart-comparison` in
`dag/nodes/sec-picard-framework/new-y3-determinant-split-chart-comparison.json` states only
common local bases, evaluation of the splitting, and bijectivity of the actual exterior
and tensor section comparison maps. Its module is
`lean/Sheaf/AlgebraicGeometry/Modules/DeterminantSplitChartComparison.lean`. Its docstring and
node give the common-frame, exterior-comparison and free-generator tensor arguments,
including edge cases. It inherits the original node's chapter and unit. There are no
statement changes or forced adaptations. The static checker conservatively flags the
namespace-local `open scoped TensorProduct`; its unchanged importer interface is documented
in `coord/changes/determinant-split-linear-bijective-notation.md`.

## Second reading by Y3

1. Compared the delivered main module with the repository using diff and extracted
   the existing theorem signature: byte-for-byte identical. Existing node changes
   are confined to proof, proof_deps and proof_origin. No target, definition or public
   signature changed. The scoped-notation change is correctly documented.
2. Compiled both modules in import order through lcompile.py: no errors or warnings.
   Reviewed every helper and the transported-map argument. Exactly one named sorry
   remains, determinant_split_chart_comparison; no forbidden declaration commands or
   hollow definitions occur. Scratch-copy #print axioms checks show only the three
   permitted axioms and the expected sorryAx for the two public theorems; the private
   algebraic helpers use only permitted axioms.
3. Read the chart statement, docstring, node and existing local exterior comparison.
   Its common free frames, evaluated splitting and actual unit/tensor comparison are
   true, needed and strictly part of the original argument. It does not restate the
   determinant conclusion: it contains no l, d or wedge-formula hypothesis. Checked
   rank-zero blocks, zero section rings and empty subopens; singleton bases work in
   all these cases. New searches with different wording through LeanFinder, Loogle
   and grep found free-sheaf APIs and TensorProduct.map_bijective, not a replacement
   for the whole chart lemma. The latter cannot be closed in a few minutes because
   it still requires compatible restriction/over-category splitting transport.
4. The direct triangular basis argument is a shorter route than expanding arbitrary
   lift differences. Proof-only imports in the main module supply exactly the new
   comparison and exterior/product/tensor bases. Both obsolete old proof dependencies
   are listed under No longer needed; the exterior comparison is moved to the new
   node, not pruned. The unchanged unit realized record contains no realization for
   this sublemma; no unit-level route is bypassed. One hole closed and one added is
   a decomposition with zero net holes, not an axiom-free completion.
5. The original node records the actual chart reduction and basis argument. The new
   node has its source, complete proof plan, search records, creation/blueprint fields
   and matching Lean declaration. Repaired its lean.statement to preserve the full
   signature verbatim, and imported ExteriorSheafLocalFreeComparison privately in
   its module so its recorded planned proof dependency is present. No statement or
   proof-body repair was needed. Added the fresh Loogle component-search result.

Second-reading changes: one proof-only dependency import, verbatim new-node Lean
signature, an additional search record, and this review report. Holes closed and
added remain exactly those listed above.
