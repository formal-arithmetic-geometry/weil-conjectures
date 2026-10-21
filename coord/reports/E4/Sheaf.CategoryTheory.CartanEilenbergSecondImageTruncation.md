## What changed

Restored `Sheaf.CategoryTheory.CartanEilenbergSecondImageTruncation` from its
quarantine archive, as required by the current rework row. Removed its obsolete
private `Sheaf.CategoryTheory.DoubleComplexTotal` import: that duplicate clashes
with the upstream double-complex declarations already publicly supplied by
`WeilConjectures.CategoryTheory.CartanEilenbergPresentation`.

The theorem `CategoryTheory.cartanEilenberg_second_image_eq_truncation`, its
signature, complete proof, docstring and public imports are unchanged. Its node
`lem-sp-ce-second-image-truncation` still describes the actual proof: top and
bottom edge cases, decalage image comparison, normalized commuting truncation
square, and cancellation of the cut isomorphism. No node route changes are
needed; its Lean attachment and all declared dependencies are preserved.

Single-file server compilation passed in 5.4 seconds without errors or warnings.
The unchanged quarantined direct consumer
`Sheaf.CategoryTheory.CartanEilenbergAcyclicAbutment` also compiled cleanly in
6.1 seconds, after compiling the restored item in the same scratch overlay. Change record:
`coord/changes/CartanEilenbergSecondImageTruncation-restoration.md`.

## Proved and sorry left

This is a zero-hole restoration repair. The archive already fully proves
`CategoryTheory.cartanEilenberg_second_image_eq_truncation`; its proof is retained.
Holes closed: 0 of 0. Holes added: 0. Sorries left: none. No result is split off.
The restoration is substantive: the archive's import collision prevents it from
compiling unchanged, and deleting the obsolete private import repairs it.

## No longer needed

Removed direct proof import `Sheaf.CategoryTheory.DoubleComplexTotal`; use its
adopted upstream declarations through the existing presentation import instead.
No mathematical dependency or DAG node is pruned, and no module is withdrawn.
The decalage/truncation diagram, decalage image theorem and their dependencies
remain needed. The two `import all` proof imports supply the private
`exists_image` and `transported_imageFiltration_eq` helpers used in the proof.

LeanFinder found only generic complex truncation and factorization results;
Loogle did not recognize the project spectral-image-filtration declaration.
Source searches found no shorter replacement for the normalized image equality.
The existing complete three-case proof is retained.

## Where the brief, the DAG or earlier work was wrong

The assigned item is absent from `lean/` because it was quarantined after a
cluster restore, not because its theorem was withdrawn. The current rework row
was read before restoring the archive; the old upstream-sync notice does not
supersede it. The archived direct Sheaf double-complex import became incompatible
with the adopted upstream declaration provider. No mathematical statement or
unit-route error was found. The archived theorem has zero sorries, so this
repair claims no newly closed hole.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
