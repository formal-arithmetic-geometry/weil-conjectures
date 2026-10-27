## What changed

The assigned module now imports `Sheaf.CategoryTheory.SignedKoszulTensorAssembly` and proves
`CategoryTheory.isColimit_ringedNegativeKoszulSummands_succ` by composing two lower,
strictly simpler statements. I added the modules `Sheaf.CategoryTheory.SignedKoszulBasisCoproduct`
and `Sheaf.CategoryTheory.SignedKoszulTensorAssembly`, together with their DAG nodes.
The basis module isolates the degreewise finite subset coproduct. The assembly module
isolates the total tensor universal-property step under those degreewise coproduct
hypotheses. No existing definitions or signatures were changed.

## Proved and sorry left

The assigned theorem `isColimit_ringedNegativeKoszulSummands_succ` is proved by a real
Lean application of the assembly theorem and the basis theorem. Two new named theorem
holes remain:

- `isColimit_ringedNegativeKoszulBasis_succ` in
  `Sheaf.CategoryTheory.SignedKoszulBasisCoproduct`, node
  `lem-cbc-signed-koszul-basis-coproduct`.
- `isColimit_ringedNegativeKoszulTensor_of_basis` in
  `Sheaf.CategoryTheory.SignedKoszulTensorAssembly`, node
  `lem-cbc-signed-koszul-tensor-assembly`.

There are no `sorry`s inside definitions or private declarations.

## No longer needed

None. The assigned module still uses `Sheaf.CategoryTheory.SignedKoszulCompletionModel`
through the new proof modules. No existing node or module was withdrawn.

## Where the brief, the DAG or earlier work was wrong

The existing DAG proof plan does not expose the two categorical substeps as Lean
statements. The finite basis coproduct and the total-tensor assembly are separate
obligations; the assigned theorem now depends on both explicitly. Searches of the local
Sheaf and WeilConjectures libraries and the available Loogle/LeanFinder results found
only generic `mapBifunctor` and colimit infrastructure, with no noncircular theorem for
this normalized negative Koszul family.

## New nodes

`lem-cbc-signed-koszul-basis-coproduct` records the degreewise supported pure-basis
coproduct and is stated in `SignedKoszulBasisCoproduct.lean`.

`lem-cbc-signed-koszul-tensor-assembly` records the total-tensor assembly conditional on
those degreewise coproducts and is stated in `SignedKoszulTensorAssembly.lean`.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
