## What changed

Replaced the sole sorry in
`AlgebraicGeometry.Scheme.Modules.finiteFree_pullback_single_iff_residue`
with a complete Lean reduction. The existing theorem signature, visibility, public
imports and docstring are unchanged. Added proof-only imports of
`Mathlib.Algebra.Homology.SingleHomology`,
`WeilConjectures.AlgebraicGeometry.Modules.FreeComplex`,
`WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel`, and the two new
modules below. Updated the assigned DAG node's proof, proof_deps and proof_origin.

The forward direction constructs a point-indexed open cover from local homotopy
normal forms, computes single-complex homology, commutes homology with exact open
restriction, and glues vanishing and finite local freeness. The reverse direction
computes the field fibre of the source complex, uses ordinary pullback composition,
and compares it with the original residue fibre. Three proved private helpers
compare ranks of matrices at field-valued points having the same image, use the
source-library rank-nullity formula to compare cohomology dimensions, and extract
single cohomology from a homotopy equivalence. The dimension comparison needs no
boundedness and handles every integer degree.

All three sandbox modules compile together in import order through lcompile.py.
The new statements were checked mathematically for r=0, i>d, d=0, and empty schemes.
If i>d and a point exists, their hypotheses force r=0. Local normal forms require no
reducedness. An empty source gives an empty point-indexed open cover; the existing
gluing lemmas cover this case without selecting a point.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.finiteFree_pullback_single_iff_residue`
(node `lem-pc-finite-free-pullback-residue-criterion`). No sorry remains in the
assigned module. Its three new private helper theorems are fully proved.

Added two holes, each the whole proof of one public theorem in its own new module:

- `AlgebraicGeometry.Scheme.Modules.exists_restrict_homotopyEquiv_single_of_residue`,
  in `Sheaf.AlgebraicGeometry.FiniteFreeResidueLocalHomotopy`, node
  `lem-pc-finite-free-residue-local-homotopy`.
- `AlgebraicGeometry.Scheme.Modules.nonempty_homotopyEquiv_single_field_fibre`,
  in `Sheaf.AlgebraicGeometry.FiniteFreeSingleFieldFibre`, node
  `lem-pc-finite-free-single-field-fibre`.

This is a decomposition, not a sorry-free proof: one upper hole closed, two lower
holes added, for a net change of minus one before any independent pruning. The
first statement produces a local homotopy equivalence at one specified point;
it contains no global image criterion or gluing. The second is a field-fibre
normal form for one complex with single locally free cohomology; it contains no
image descent or residue comparison. Both supply explicit homotopy information
used by the proved argument. Neither is the original equivalence repackaged.

## No longer needed

No import from the original module was removed: all three original public imports
remain required by the unchanged statement. The original file had no proof imports.
The new modules expose only the imports their statements need. Removed the unused
SingleHomology import from their draft headers, retaining it as a proof-only import
of the assigned module, and removed ResidueField from the field-fibre draft header.

Pruned from the assigned node's direct proof route:

- `lem-pc-finrank-field-base-change` (`Module.finrank_baseChange`,
  `Mathlib.LinearAlgebra.Dimension.Constructions`): not used even in the two new
  normal-form statements' plans. Equal-image matrix-minor ranks and the already
  proved fibre rank-nullity formula replace field-extension dimension descent.
- `lem-pc-ringed-spaces-derived-pullback-composition`, module
  `Sheaf.AlgebraicGeometry.DerivedPullbackComposition`: not needed in this reduction
  or the new statements' plans. Composition in the proved argument is ordinary
  `Modules.pullbackComp`, not a derived-composition theorem.

The following old direct dependencies remain needed below the new intermediate
nodes, and are not claimed as globally pruned:

- `lem-weil-pbc-free-complex-unit-entry-splits`, module
  `Sheaf.Algebra.Homology.UnitEntrySplits`, for local cancellation in the first node.
- `lem-pc-flat-complex-derived-pullback`, module
  `Sheaf.AlgebraicGeometry.FlatComplexDerivedPullback`, for the second node's
  flat-single fibre calculation.

No claim is made that modules still reached through other targets have become
unreachable. The import-closure ledger decides that.

## Where the brief, the DAG or earlier work was wrong

The original planned dependencies are not enough to apply directly to this module:
UnitEntrySplits is a chain-complex statement over a ring, while this module needs
cancellation spread to open neighbourhoods of schemes and preserved by pullback.
FlatComplexDerivedPullback uses the ringed-space module carrier and does not itself
state the fibre normal form following truncation. The two new nodes isolate those
missing bridges, with complete proof sketches in their docstrings and node files.

The unit route is preserved: finite free cancellation, a flat single cohomology
fibre, and cohomology descent from a source point. Only the final scalar-extension
calculation is replaced by a proved matrix-minor argument below the unit level.
No statement or definition was changed, and no forced adaptations were needed.

The blueprint markdown is absent in this read-only clone. The source was read from
the assigned module's full docstring and the recorded proof steps in its DAG node,
as the brief provides; the existing unit record was also read. The new nodes keep
that source attribution and mark their proof origin as agent-written. Searches of
the blueprint index found no existing local normal-form node. LeanSearch returned
Internal Server Error; both new nodes record it as unavailable, not as no match.
LeanFinder, Loogle and Mathlib grep searches ran and are recorded with their actual
queries and results. The existing DerivedPullbackSingleCohomology and
DerivedSingleOpenLocus modules import the upper FiniteFreeComplex module and would
create an import cycle if used here, so neither was imported.

## New nodes

`lem-pc-finite-free-residue-local-homotopy`, module
`Sheaf.AlgebraicGeometry.FiniteFreeResidueLocalHomotopy`: local cancellation at one
residue point, spreading the finite collection of matrix identities, and pulling
back the resulting homotopy equivalence to a source neighbourhood. Its proof plan
uses the existing unit-entry splitting node. Empty sources make its pointwise
statement vacuous; rank zero gives a contractible complex.

`lem-pc-finite-free-single-field-fibre`, module
`Sheaf.AlgebraicGeometry.FiniteFreeSingleFieldFibre`: truncate to the flat cohomology
sheaf in degree i, calculate its derived field fibre using bounded flat complexes,
and split the resulting vector-space complex into cohomology and contractible
summands. Its plan uses the existing flat-complex derived-pullback node. It has no
image comparison and applies to an arbitrary field-valued point.

No change record is required: there is no existing interface change.

## Second reading by M2

1. **Interface and accidental changes.** Compared the assigned module with the repository version. The theorem signature, visibility, docstring, and public imports needed by the statement are unchanged; only proof imports, proof text, and the node's proof metadata changed. The two added modules contain the new split statements recorded in their nodes.

2. **Compilation and proof hygiene.** Compiled all three modules with `lcompile.py --all`; all compile successfully. The assigned theorem has no `sorry`, and the only remaining `sorry`s are the two named public split theorems, each with a docstring proof and matching DAG node. No `axiom`, `unsafe`, `opaque`, `extern`, `implemented_by`, or sorry in a definition was found.

3. **Statement checks.** Read each split statement against its declaration and tested the edge cases described in the report (rank zero, degree outside the support, dimension zero, and empty source). Both are strictly lower-level reductions: one is local homotopy normal form, and the other is a field-fibre homotopy normal form; neither restates the assigned equivalence. Searches recorded in the node found no existing Mathlib or library theorem with either statement.

4. **Proof route and pruning.** The proof uses the two split theorems and the explicit matrix-minor rank comparison. The finite free cancellation, flat fibre, and ordinary pullback composition route is retained through the split nodes. The old field-dimension and derived-composition dependencies are no longer used and are recorded under `## No longer needed`; imports of the assigned theorem's statement remain public, while new proof-only imports are plain imports.

5. **DAG and unit agreement.** Checked the three node records: declarations, statements, proof steps, proof dependencies, source, and proof origins agree with the Lean files. The unit `sk-thm-picard-perfect` route remains represented by the cancellation and flat-fibre dependencies. No definition or target statement was changed.

I changed only the proof imports and proof of the assigned module, added the two split modules and their DAG nodes, updated the assigned node's proof metadata, and appended this review.
