## What changed

Added the auxiliary module `Sheaf.CategoryTheory.Sites.EtaleTorsorInverseImageExtensionAux`.
The original theorem now combines two strictly smaller named intermediate theorems: one for
constructing the inverse-image torsor and equivariance, and one for the remaining extension data.
Both auxiliary theorem proofs are still open and are explicit named `sorry`s.

## Proved and sorry left

The parent declaration `CategoryTheory.Sheaf.Torsor.etale_torsor_inverse_image_extension`
is reduced to the two auxiliary declarations and has no direct `sorry`.
The following two new declarations retain `sorry` proofs:

- `CategoryTheory.Sheaf.Torsor.etale_torsor_inverse_image_torsor`
  (node `new-etale-torsor-inverse-image-torsor`)
- `CategoryTheory.Sheaf.Torsor.etale_torsor_inverse_image_extension_core`
  (node `new-etale-torsor-inverse-image-extension-core`)

## No longer needed

None. The original imports remain needed by the auxiliary statements and the parent theorem.

## Where the brief, the DAG or earlier work was wrong

The DAG proof plan was too large for one directly elaborated theorem. Splitting it at the
construction of the inverse-image torsor makes the dependency boundary explicit while preserving
the parent statement unchanged.

## New nodes

`new-etale-torsor-inverse-image-torsor` records the torsor transport subargument.
`new-etale-torsor-inverse-image-extension-core` records the extension and uniqueness subargument.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
