## What changed

Proved the coefficient-map, tensor Hom extension, functor, natural-transformation,
composition, whiskering, exactness and exact-comparison clauses of
`Sheaf.CategoryTheory.SemilinearScalarLocalization`, without changing any existing
signature, visibility or definition. The Hom map is obtained directly from Mathlib's
balanced additive tensor universal property, rather than first passing through a
localized module. Private proved helpers record the pure-tensor specification and
heterogeneous extensionality. Updated the existing node's proof route accordingly.

## Proved and sorry left

Closed all 19 of the original 19 holes, all in namespace
`CategoryTheory.ScalarLocalization`:

- `coefficientMap_unique`
- `existsUnique_semilinearHom`
- `extensionHom_laws`
- `extension_spec`
- `extension_unique`
- `existsUnique_semilinear_extension`
- `extensionNatTrans_naturality`
- `extensionNatTrans_unique`
- `extensionNatIso_spec`
- `extensionNatTrans_laws`
- `extension_comparisonSquare`
- `semilinear_composition`
- `extension_comp`
- `extensionNatTrans_whiskerRight`
- `extensionNatTrans_whiskerLeft`
- `isSemilinear_of_linear`
- `extension_id_and_linear`
- `extension_exact`
- `extension_exactComparison`

Added zero holes and zero split-off statements. No `sorry` remains in the module.
The completed `extension_exact` uses Mathlib's coherent `commShiftOfLocalization`.
A private tensor comparison with the existing `Rationalization` establishes that the
raw localization functor is a categorical localization; it follows the construction
already proved in `ScalarLocalizationTriangulated`. The normalized integral comparison
then gives the required HEq component formula. The two image-triangle descriptions
prove preservation of distinguished triangles, using the composition comparison.
Private helpers transport addition, functor maps and inverses across equal endpoints.

Validation: the retained full module compiled cleanly through `lcompile.py` in 5.7 seconds
with all 19 proof holes closed, no warnings, and no overlength lines.
No existing declaration signature, visibility or definition was changed.

## No longer needed

Removed the redundant proof import `Sheaf.CategoryTheory.ScalarLocalization`
(already publicly imported by `ScalarLocalizationTriangulated`). Removed proof imports
`Mathlib.RingTheory.Localization.BaseChange` and
`Mathlib.Algebra.Module.LocalizedModule.Basic`. The proof does not use nodes
`def-weil-pbc-module-localization-away` or
`lem-weil-pbc-localization-module-tensor`: the raw Hom spaces already are tensor
products, and `TensorProduct.liftAddHom` constructs their balanced map directly.
Their dependency entries were removed from the node's proof and proof_deps.
The two removed Mathlib imports are direct-import removals; the new proof import
`WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom` itself
imports tensor localization. Thus this does not claim that BaseChange leaves the
transitive import closure. Also added the proof import
`Mathlib.CategoryTheory.Shift.Localization` for coherent shift descent.
No project module is withdrawn. The public triangulated-localization import remains
because the exactness clause still uses its induced structures and triangle description.

## Where the brief, the DAG or earlier work was wrong

No statement defect found. The DAG's module-localization construction is valid but
longer than the direct balanced tensor map. Functor equality requires explicit care
with dependent object equalities; the uniqueness and whiskering proofs use HEq only
for equal endpoints, as intended by the original interface.

The resumed worker retained the completed proofs and verified them against the current
sources. Only `proof`, `proof_deps` and `proof_origin` differ in the node copy.
The earlier dry run passed at commit `b247f89f00`; a fresh dry run is being run before
submission. Earlier delivery attempts encountered shared-worktree capacity delays and
a temporary-worktree checkout timeout, before submission.

## Second reading by A2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
