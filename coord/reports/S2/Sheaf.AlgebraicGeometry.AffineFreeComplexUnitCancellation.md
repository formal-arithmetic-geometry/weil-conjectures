## What changed

Completed the proof of `AlgebraicGeometry.Scheme.Modules.exists_affine_free_complex_unit_cancellation`
in `Sheaf.AlgebraicGeometry.AffineFreeComplexUnitCancellation` without changing its signature.
It lifts the original affine complex, applies the proved unit-entry splitting, contracts the
identity summand, maps the homotopy through tilde, reverses the grading, and derives the precise
rank formula. The unaffected-term isomorphisms follow from the same free-sheaf sizes.
Private helpers explicitly reverse complexes, maps, homotopies and homotopy equivalences.

Added `Sheaf.Algebra.Homology.SplitIdentityHomotopyEquiv`, fully proved. It constructs the
complementary and identity-summand projections and inclusions, contracts the two-term complex,
and combines the resulting homotopies. Added `Sheaf.AlgebraicGeometry.AffineFreeComplexModuleLift`
for the original-complex lifting and unit-coefficient compatibility step, left for another worker.
Both new statements have separate DAG nodes; the original node now follows the Lean argument.

## Proved and sorry left

Closed the original hole:
`AlgebraicGeometry.Scheme.Modules.exists_affine_free_complex_unit_cancellation`
(`lem-pc-affine-free-complex-unit-cancellation`). This is a decomposition from one smaller
remaining theorem, not a sorry-free proof of the affine cancellation result.

Fully proved the new theorem `ChainComplex.nonempty_homotopyEquiv_of_split_identity`
(`lem-pc-split-identity-homotopy-equiv`) and its private binary-sum and contraction helpers.

Added exactly one hole, the entire proof of
`AlgebraicGeometry.Scheme.Modules.exists_affine_free_complex_module_lift`
(`lem-pc-affine-free-complex-module-lift`). It asserts no cancellation, complement or homotopy
equivalence: it only lifts the original complex and its supplied unit coefficient.
No other delivered declaration contains sorry. Original holes closed: 1; holes added: 1;
net holes closed: 0. There are no data definitions chosen from the unproved lifting theorem;
the main proof eliminates its existential statement locally inside a theorem proof.

The lifting docstring supplies the full argument, including standard-basis and global-sections
compatibility. Edge cases checked: the supplied indices exclude zero-sized source or target
bases, natural subtraction agrees with the splitting's successor equations, and the zero ring
is allowed. The contraction proof uses subsingleton terms rather than a nontriviality assumption.

## No longer needed

Removed the direct proof import `Mathlib.AlgebraicGeometry.Modules.Tilde` from the original
module; the proof import of `AffineFreeComplexModuleLift` already supplies that dependency.
No existing DAG node or library module is pruned. In particular
`lem-weil-pbc-free-complex-unit-entry-splits` / `Sheaf.Algebra.Homology.UnitEntrySplits` and
`lem-weil-pbc-spec-tilde-free-module` remain needed. No planned unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The statement and planned route are mathematically consistent. The DAG called contraction
an elementary step but supplied no Lean interface for it; that step is now fully implemented.
LeanSearch returned Internal Server Error, so the unavailable searches are recorded honestly;
Loogle, LeanFinder, Mathlib source and blueprint searches found no complete replacement.

An explicit affine-lifting attempt constructed the free modules, lifted differentials and
square-zero proofs, but did not finish the dependent standard-basis and coefficient transports.
The saved draft in `scratchpad/AffineFreeComplexModuleLift-attempt.txt` is not part of the delivery.
The deliverable leaves this entire affine comparison step as one sourced public theorem.

Sources were read at https://stacks.math.columbia.edu/tag/00MT,
https://stacks.math.columbia.edu/tag/01HV and https://stacks.math.columbia.edu/tag/01I7.
No existing signatures, definitions, target statements or public imports were changed.

The required dry run failed before compilation or preflight, with:
`FAILED: missing import source modules`, naming standard Mathlib modules
`Mathlib.Algebra.Category.ModuleCat.Basic`, `Mathlib.Algebra.DirectSum.Module`,
`Mathlib.Algebra.Homology.Homotopy`, `Mathlib.Algebra.Homology.HomologicalComplex`,
`Mathlib.AlgebraicGeometry.Modules.Tilde`, and `Mathlib.LinearAlgebra.Matrix.ToLin`.
These imports exist in the supplied read-only Mathlib source tree and all three delivered
modules compiled cleanly with lcompile.py --all. The delivery tool's import-source validation
is therefore blocked by its source inventory/path configuration. No tool was edited or bypassed,
and nothing was pushed. The second reader can rerun the dry run after the tool is repaired.

## New nodes

`lem-pc-affine-free-complex-module-lift`: new module
`lean/Sheaf/AlgebraicGeometry/AffineFreeComplexModuleLift.lean`, with exactly one public theorem
and one sorry. It is step 1 of the original argument, strictly before the algebraic splitting.

`lem-pc-split-identity-homotopy-equiv`: new module
`lean/Sheaf/Algebra/Homology/SplitIdentityHomotopyEquiv.lean`, fully proved from Mathlib.
It isolates the supplied-splitting contraction independently of rank and affine geometry.

No change records or forced adaptations are required.

## Earlier second reading (a previous round; superseded)

Pending independent second reading; the delivered modules compile and the declarations match their DAG statements.

## Second reading by S2

1. **Visible declarations and statements.** Compared the delivered cancellation module with the repository version. The target declaration has the identical signature; only its proof and proof-only imports changed. The two added public declarations are new DAG nodes and do not alter existing declarations.

2. **Compilation and proof integrity.** Compiled all three sandbox modules with `lcompile.py --all`; all compiled cleanly. Searched delivered Lean sources for forbidden constructs: the only remaining `sorry` is the named theorem `exists_affine_free_complex_module_lift`, with its source and proof sketch in the docstring and matching node. The split-identity theorem and the target proof contain no `sorry`.

3. **New statements.** Checked the lifting theorem's hypotheses and conclusion against the cancellation proof: it only supplies a module complex, bases, the transported unit coefficient, and the tilde comparison required downstream; it does not assert cancellation. Checked the split-identity theorem: it gives precisely the homotopy equivalence from the explicit differential-compatible direct-sum splitting. Both are strictly smaller than the target and are not duplicates of existing declarations found by repository searches.

4. **Route and pruning.** The target proof follows the planned route through affine lifting, unit-entry splitting, identity-summand contraction, tilde transport, and degree reversal. The unit-entry-splitting and tilde-free-module dependencies remain used. The direct Tilde import removed from the target module is supplied through the lifting module, so no proof dependency is lost; no existing node is pruned.

5. **DAG consistency.** Checked the three node files against the declarations and proof calls. The target node records the lifting and split-identity nodes in its proof dependencies; each new node records its module, declaration, source, and split status. The unit's planned route is retained.

I added this second-reading section; no Lean source or node statement required repair.
