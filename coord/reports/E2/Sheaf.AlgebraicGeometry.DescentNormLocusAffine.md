## What changed

Replaced the sole sorry in `Sheaf.AlgebraicGeometry.DescentNormLocusAffine` with a
complete Lean reduction. The signature and existing docstring are unchanged.
A private, proved helper `mem_basicOpen_norm_of_free` generalizes the geometric
argument in the existing `BaseChangeNorm` module by taking freeness explicitly.
It applies the already proved `Algebra.norm_notMem_iff` on affine section spectra.
The main proof pulls f back via `t.appLE`, applies the new norm-chart construction,
proves the fibrewise nonvanishing condition, identifies U with the norm basic open,
restricts the norm to D(f), and applies `IsAffineOpen.basicOpen` twice.

Added the proof imports `Sheaf.AlgebraicGeometry.FiniteLocallyFreeNormCharts` and
`WeilConjectures.Mathlib.RingTheory.Localization.NormTrace`. The new module states
only the norm construction on finite free charts, without any affineness conclusion.
Its source and full construction/gluing argument are in its docstring and node.
The original node now follows the actual Lean proof. A second new node records
an existing proved ring criterion, so that the DAG names the tool the proof uses.
No existing signature, definition, or public import changed; no forced adaptations.
Both delivered Lean modules compile with no errors or warnings through lcompile.py.

## Proved and sorry left

Closed the original hole in
`CategoryTheory.Over.DescentDatum.isAffineOpen_descent_norm_locus`
(node `lem-pd-descent-norm-locus-affine`). No sorry remains in the item's module.
The private helper `mem_basicOpen_norm_of_free` is fully proved as well.

Added one hole:
`AlgebraicGeometry.exists_finiteLocallyFree_norm_charts`
(node `lem-pd-finite-locally-free-norm-charts`, module
`Sheaf.AlgebraicGeometry.FiniteLocallyFreeNormCharts`). This is exactly `by sorry`.
It constructs a norm section and local finite free determinant charts; it asserts
no affine locus and has none of the affine-open containment hypotheses of the
original statement. The fibre criterion and final affine argument are proved here,
so this is a strict decomposition, not a renamed original statement. One hole closed,
one added: net zero holes; this delivery is a decomposition, not a complete proof
of the norm construction. `Algebra.norm_notMem_iff` is already proved in the library
and adds no hole.

Edge cases checked in the mathematical statements: empty W makes the chart condition
vacuous; an empty source gives rank-zero norm 1 and a vacuous fibre criterion; no
surjectivity or positive constant rank is assumed. For s the identity the charts give
the ordinary rank-one norm. Varying rank is handled locally, and no arbitrary witness
is used to define data: the existential norm is eliminated only in the proof.

## No longer needed

No original imports, nodes, or modules were pruned. Both original DAG dependencies
(`def-pc-scheme` and `def-pc-finite-locally-free`) remain needed in the construction
node's statement and proof. They now occur below that node rather than as the
original theorem's immediate proof dependencies.

The field-extension specialization in `WeilConjectures.AlgebraicGeometry.BaseChangeNorm`
was read but is not imported or used as a dependency; the proof uses the general ring
criterion directly, avoiding its field-extension and flat-descent infrastructure.
No claim is made that those modules are globally unreachable from other targets.
The unit record `sk-prop-jacobian-descent` is unchanged; its route is retained.

## Where the brief, the DAG or earlier work was wrong

The original node's single proof step names only scheme and finite-locally-free
notions. Those declarations do not supply the glued norm section or local norm
charts. That substantial construction is now an explicit, strictly intermediate
statement; all the remaining geometry and affine basic-open glue are proved.
No mathematical statement was disputed or weakened.

LeanSearch was attempted for both new nodes but returned Internal Server Error.
Loogle, LeanFinder, local Mathlib/source searches, and blueprint searches were used
instead, with the failed search recorded as unavailable. Stacks Tag 03JE was read;
its final norm argument is the source of the construction and locus criterion.

## New nodes

`lem-pd-finite-locally-free-norm-charts` records the one remaining construction:
a section g on W whose restrictions on an affine finite free neighbourhood of each
point are the determinant norms of the source section. It lives in its own new
module, with its Lean signature recorded verbatim. Local freeness, determinant
restriction and basis independence, and sheaf gluing are described in the proof.

`lem-pd-finite-free-norm-prime-criterion` records the already proved
`Algebra.norm_notMem_iff` in `WeilConjectures.Mathlib.RingTheory.Localization.NormTrace`.
It adds no module and no sorry. The node gives the localization, unit, and going-up
argument of the existing source proof. No change record is required.

## Second reading by E2

1. Compared the delivered target module with the repository version. Existing
declaration signatures and docstrings are unchanged; only proof code and proof-only
imports were added. Verdict: pass.

2. Compiled both delivered modules with `lcompile.py --all`. The target has no
`sorry`, `axiom`, `unsafe`, `opaque`, `implemented_by`, or `extern`; the only
remaining `sorry` is the named construction theorem in its own module. Scratch-copy
`#print axioms` checks give only the three permitted axioms plus `sorryAx` for the
target and construction, and only the permitted axioms for `Algebra.norm_notMem_iff`.
Verdict: pass.

3. Checked the split construction and criterion statements against the Lean
declarations, their docstrings, and the DAG nodes. The construction is a strict
intermediate result and the criterion records the existing proved ring lemma.
Edge cases in the report are covered by the statements. Independent LeanFinder
search for determinant norm sections returned normalization and structure-sheaf
results, not a norm construction. Loogle confirmed `Algebra.norm_localization`
as the relevant partial tool. Local source searches found only the field-extension
specialization. Read Stacks Tag 03JE directly and checked its norm argument.
Verdict: pass.

4. Reviewed the proof route and imports. The proof uses the local norm-chart
construction, the existing norm prime criterion, and affine basic-open lemmas; no
shorter applicable library theorem was found. The unit route remains unchanged and
no unused original dependency was removed. Verdict: pass.

5. Checked that the target node proof steps and `proof_deps` match the Lean proof,
and that both new nodes have the required source, proof, search, Lean, unit, and
chapter fields. Verdict: pass.

Second reading changed only this report, adding the review and verification evidence.
The first worker's Lean code and nodes needed no repairs. No statement or definition
was changed. The remaining norm construction requires the substantial local-freeness
and gluing argument documented in its docstring; it was not closed in this reading.
