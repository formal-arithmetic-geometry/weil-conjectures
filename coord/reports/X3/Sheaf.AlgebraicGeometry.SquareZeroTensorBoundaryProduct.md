## What changed

Replaced the sorry in
`AlgebraicGeometry.Scheme.Modules.transportedTensorBoundary_product` with a complete
Lean proof from the existing `AlgebraicGeometry.boundary_derivation_square_zero` and
a new homogeneous realization/comparison theorem. The original theorem's signature,
public imports and comparison definitions are unchanged.

The new module is
`Sheaf.AlgebraicGeometry.SquareZeroTensorBoundaryGradedRealization`. Its theorem
`AlgebraicGeometry.Scheme.Modules.tensorBoundary_graded_realization` isolates steps
1 and 3 of the original plan: realize the tensor sequences inside a square-zero
algebra extension and compare its three degree projections with the canonical
boundaries and coefficient actions. It gives two action squares for EVERY cohomology
class, three separate boundary comparisons, and no Leibniz identity. It is a geometric
comparison statement, not the product identity under another name.

The product proof applies the existing square-zero algebra boundary theorem to that
extension, supplies its resolution/action/boundary specifications to the comparison
property, applies an additive projection to its Leibniz identity, and identifies the
three supplied classes using inverse laws of the additive equivalences. All these
steps are written in Lean; no sorry remains in the product proof. No definition or
existing statement is changed, and there are no forced adaptations.

Compilation diagnosed a slow broad rewrite of the cohomology expressions. Scoped
profiling of successive prefixes showed that obtaining the extension, resolutions
and comparison data was inexpensive. Replacing the final `rw`/`simp` traversal with
explicit `congrArg`, inverse-equivalence laws and a `calc` chain compiled the first
version in 24.2 seconds. Explicit class types on the universal action-square binders
also avoid expensive inference in the strengthened realization statement. Diagnostic
profiler options and temporary partial proofs have been removed from the delivery.

## Proved and sorry left

Closed one upper hole:
`AlgebraicGeometry.Scheme.Modules.transportedTensorBoundary_product`
(node `lem-sc-square-zero-tensor-boundary-product`).

Added one named intermediate hole:
`AlgebraicGeometry.Scheme.Modules.tensorBoundary_graded_realization`
(node `lem-sc-square-zero-tensor-boundary-graded-realization`), whose proof is exactly
`:= by sorry` in its own module. It has its source and a complete construction/comparison
argument in its docstring and node. This is a decomposition: one hole closed and one
added, net zero; it is not a completed proof of the graded realization. There are no
other added holes and none left in the item's module. The existing algebra boundary
theorem is used as provided by the library.

The new statement was checked mathematically for n=0, e=0, a zero ideal, and zero
sections. Projection to degree zero is still a single homogeneous projection, even
when n=0 makes the three numerical degrees equal; the three coefficient targets are
related by the canonical unitors. A zero ideal has zero kernel cohomology and zero
boundaries. Zero sections give zero homogeneous elements and zero action maps. There
is no characteristic, Noetherian, separatedness or finite-type hypothesis added.
The construction does not require H1 to commute with infinite sums: it uses only H1
of each inclusion and projection. Local polynomial descriptions are sheaf-local;
no false assertion about global sections commuting with infinite direct sums is used.

## No longer needed

Removed these four direct proof imports from the item's module:

- `Sheaf.AlgebraicGeometry.AffineMorphismCohomologyEdge`
- `Sheaf.AlgebraicGeometry.ClosedImmersionUnitQuotient`
- `Sheaf.AlgebraicGeometry.ModuleCohomologyBoundary`
- `Sheaf.AlgebraicGeometry.SectionBoundaryExact`

The product proof's direct proof dependencies are now precisely the new realization
node and `lem-sc-boundary-derivation-square-zero`. The original unit-quotient,
ideal-tensor comparison, ideal-powers, affine-edge and canonical boundary nodes are
needed by the realization/comparison argument or by the public statement imports;
they have not been mathematically pruned. No whole module is claimed to leave the
target import closure. The public comparison and ClearDenominators imports remain.

## Where the brief, the DAG or earlier work was wrong

The original DAG describes the graded-algebra construction and homogeneous comparison
in words, but none of its listed declarations states those combined interfaces.
The existing boundary theorem is about sections of algebra sheaves, whereas this
item is about line-bundle tensor degrees with canonical coefficient comparisons.
The missing bridge is now an explicit independently provable theorem. The unit route
is retained: `sk-thm-curveestimate` realizes `thm-sc-proper-cohomology`, and this change
is below its unit level and keeps the prescribed square-zero derivation argument.

The local clone does not contain the literature files listed as obtained. The Stacks
09MS and 0B8S pages and their TeX sources were read directly; source copies for this
session are in the sandbox scratchpad, excluded from the delivery.

`tools/blueprint_refs.py ancestor lem-sc-square-zero-tensor-boundary-product` returns
None because its `created.item` records a module name rather than a node id. The new
node preserves the explicit blueprint ancestor already recorded by the parent,
`lem-sc-pic-proper-ntorsion`, and prepends the parent to its recorded via chain; no
unowned field of an existing node is edited to repair this older bookkeeping issue.

The new node's proof plan uses the generic tools
`lem-pur-ringed-site-grothendieck-abelian` (exact coproducts of module sheaves) and
`lem-sc-p1-right-derived-triangle-connecting` (snake/triangle boundary identification).
These are tools for the homogeneous construction/comparison; they do not replace
any step of the curve unit. The maintainer may record them as tool uses if required.

## New nodes

`lem-sc-square-zero-tensor-boundary-graded-realization`, in
`dag/nodes/sec-curve-estimates/`, states the square-zero algebra extension realization
and three additive degree projections, with individual boundary comparisons and
universal action squares. It deliberately does not assert an algebra or tensor
Leibniz identity. Its source is Stacks 09MS, `coherent-equation-ses` and the following
graded direct sum, and 0B8S, `cohomology-lemma-boundary-derivation-over-cup-product`,
the paragraph defining the quotient action. LeanFinder returned cotangent and
cochain results, with no matching sheaf theorem; the Mathlib grep returned no hits;
LeanSearch returned Internal Server Error and is recorded as unavailable. Repository
and whole-blueprint searches found no existing realization statement. No change
record is needed because every existing signature and definition is preserved.

## Second reading by X3

1. Compared the delivered product module with the repository version. The theorem
   signature and existing declarations are unchanged; only the proof and
   proof-only imports differ. The realization module is a separately named split
   intermediate node.
2. Compiled both delivered modules with `lcompile.py --all`; compilation succeeds.
   The only remaining `sorry` is the named realization theorem, with no forbidden
   declarations or hollow definitions.
3. Checked the split statement against its node and source, including degree-zero,
   zero-ideal, and zero-section cases. It is strictly weaker than the product
   identity because it asserts separate boundary and action comparisons and no
   Leibniz rule. Searches found no duplicate declaration.
4. Verified the proof route through the existing square-zero derivation theorem and
   comparison interface. The four old proof-only imports are removed and recorded
   above; public imports remain.
5. Verified the DAG proof, `proof_deps`, `proof_origin`, Lean declaration, and unit
   route agree. The realized unit `sk-thm-curveestimate` remains in force.

No further changes were required in this second reading.
