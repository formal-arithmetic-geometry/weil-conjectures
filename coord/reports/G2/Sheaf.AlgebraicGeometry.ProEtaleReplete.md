## What changed

Proved `AlgebraicGeometry.Scheme.isReplete_proEtale` in
`Sheaf.AlgebraicGeometry.ProEtaleReplete`, with its signature and public imports unchanged.
For any epimorphic inverse sequence, the stated w-contractible affine covering gives a
covering sieve. The proved source theorem `ProEt.isWeaklyContractible_of_iso` supplies
weak contractibility of each cover member at section universe `max (u + 1) w`.
`proetale_surjective_sections_of_epi_tower` then lifts each restricted section. Downward
closure of the image sieve proves local surjectivity and hence epimorphy of every limit
projection. This keeps both steps of unit `sk-prop-pe-replete`.

Replaced the proof import `Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences`
with `WeilConjectures.AlgebraicGeometry.ProEtale.WeaklyContractible`. Updated the node's
proof and proof dependencies to cite the existing closed source attachment
`lem-weil-pbc-source-affine-wcontractible-evaluation` for this step. It is a generic
already-proved tool; no new node or unit-level route change is needed.

LeanFinder, Loogle and Mathlib grep were run through `msearch.py`; no complete repleteness
theorem matched. The existing local-surjectivity criterion and the source affine
weak-contractibility theorem provide precisely the required glue. The single-file
launcher compile passed in 2.2 seconds. Empty schemes, empty covering families and
arbitrary indices require no extra hypotheses: the covering-sieve proof applies directly.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Scheme.isReplete_proEtale`
(node `det-pe-replete-epimorphism`). No holes remain in the item and no holes were added.
No statements were split off. The proof uses the existing stated theorem
`AlgebraicGeometry.Scheme.proetale_surjective_sections_of_epi_tower`
(node `det-pe-replete-on-contractible`), whose existing sorry remains in its own module;
that module is not changed by this delivery.

## No longer needed

Removed the direct proof import
`Sheaf.AlgebraicGeometry.ProEtale.WeakContractibleEquivalences`; node
`det-pe-weak-contractible-equivalences` is not used in this theorem's proof.
Its general equivalence of projectivity and evaluation surjectivity is unnecessary:
the source affine weak-contractibility theorem directly supplies the exact predicate.
The module remains a transitive dependency of the existing sectionwise tower module;
this delivery does not claim to remove it from the targets' entire import closure.
No other original dependency is pruned. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The DAG's selected weak-contractibility equivalence has only section universe `u + 1`
in its Lean signature, whereas the assigned repleteness theorem allows arbitrary `w`.
The closed source theorem recorded by
`lem-weil-pbc-source-affine-wcontractible-evaluation` is universe-polymorphic and
supplies the required predicate directly. This corrects the dependency choice while
preserving the mathematical argument, all hypotheses and the target signature.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
