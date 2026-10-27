## What changed

Proved `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorProduct` without
changing its statement. Three proved private helpers establish finite presentation of
ordinary module tensor products, of tilde modules, and of tensors on affine schemes.
The public theorem applies the affine result after restricting to the affine-open cover,
then uses locality for open immersions. The declaration's proof documentation and its
existing DAG node now describe this route.

Added private proof imports of `Mathlib.Algebra.Module.Presentation.Finite`,
`Mathlib.Algebra.Module.Presentation.Tensor`,
`WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent`, and
`WeilConjectures.AlgebraicGeometry.Modules.AffineTildeTensor`.
Retained `WeilConjectures.AlgebraicGeometry.Modules.RestrictionTensorComparison`.
No existing module besides the item is changed. There are no direct Lean importers of
the item in the current source tree, so no consumer adaptation is needed. The DAG parent
`lem-trf-invertible-fp-tensor-models` still needs exactly the unchanged theorem.

The remote compiler accepted the full proof in 10.6 seconds, and `#print axioms`
reported only `propext`, `Classical.choice`, and `Quot.sound`. The final file also compiled
cleanly in 14.1 seconds after removing unused imports and the diagnostic command.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.Scheme.Modules.isFinitePresentation_tensorProduct`
(node `lem-trf-fp-sheaf-tensor-product`). Proved 1 of 1 original sorries.
Added zero holes; split off zero statements. No sorry remains in the item.
All three private helpers have complete proofs. No theorem or definition signature changed.

## No longer needed

Removed the unused proof imports:

- `Mathlib.AlgebraicGeometry.Modules.Sheaf` (available through the statement imports).
- `WeilConjectures.Algebra.Homology.ModuleStalkExact`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.StalkTensor`.
- `Mathlib.LinearAlgebra.TensorProduct.RightExactness`.

Removed unused public imports `Sheaf.CategoryTheory.RingedSiteModules` and
`Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`. The statement uses
Mathlib's scheme module category and the monoidal structure already provided by
`WeilConjectures.AlgebraicGeometry.Modules.Invertible`; it needs neither of these imports.
The public-import pruning is recorded in
`coord/changes/r8-finite-presentation-tensor-imports.md`.

The proof no longer directly requires DAG nodes
`lem-weil-pbc-module-stalk-exact`,
`lem-pc-sites-sheaf-tensor-bilinear-universal`,
`lem-weil-pbc-module-stalk-tensor`, or
`lem-weil-pbc-tensor-right-exact`. The sheafification tensor definition
`def-pur-sheaf-tensor-product` remains a statement dependency, but is no longer a separate
proof dependency. The affine comparison results can themselves use stalk or tensor
lemmas internally; these are not claims of global library withdrawal. No module is deleted.

The replacement route uses existing nodes
`lem-weil-pbc-finite-presentation-affine-sections`,
`lem-weil-pbc-affine-tilde-gamma-adjunction`, and
`lem-weil-pbc-affine-tilde-tensor`, while retaining the restriction and restriction-tensor
comparison nodes. The blueprint unit route is preserved: only the proof of this
finite-presentation sublemma changes, and no unit statement or step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The statement and original mathematical argument are correct. The existing source
library theorem `isFinitePresentation_tensorObj` assumes an invertible factor, so it
cannot directly prove this item. However, the existing affine comparison API allows a
shorter proof than separately implementing the proposed sheaf stalk kernel chase.
Mathlib's `Module.Presentation.tensor` supplies the finite generator/relation argument.
Searches used LeanFinder, Loogle, the prescribed grep service, and local source searches.
Edge cases remain included: empty schemes, zero ranks, the zero ring, and non-flat
finitely presented modules. No additional flatness or Noetherian hypothesis is used.

## Second reading by R8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
