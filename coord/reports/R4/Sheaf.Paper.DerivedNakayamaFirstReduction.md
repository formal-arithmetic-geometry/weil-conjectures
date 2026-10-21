## What changed

Proved `AlgebraicGeometry.ProEtale.derived_nakayama_first_reduction` in
`Sheaf.Paper.DerivedNakayamaFirstReduction`, with its statement unchanged.
The proof uses the already stated completion triangle comparison for cones and
shifts. A private proved extensionality lemma identifies the scalar endomorphisms
from the resolution and principal cone calculus. Their cone comparisons then
identify tensor reduction with the canonical reduction after restriction.
Induction on the successive coefficient triangles proves levelwise vanishing.
The product of the zero tower is constructed directly by its universal property;
the canonical Roos triangle and completeness prove vanishing of the original object.
The left adjunction shows that its finite-coefficient reductions vanish. Finally
exact first integral reduction and the zero-cone criterion detect isomorphisms.
Updated the node proof to record these arguments. All public imports and existing
signatures are unchanged; the only private proof import is now the completion
triangle comparison. No definition or statement repair was needed.
The added proof scopes and elaboration options are recorded in
`coord/changes/R4-derived-nakayama-first-reduction-proof-scopes.md`, with all
129 transitive consumers checked for unchanged public interfaces.
The delivery compile and axiom probe passed; the first preflight requested this
command-scope change record, now supplied.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.derived_nakayama_first_reduction`
(node `det-pe-derived-nakayama-first-reduction`).
Zero holes remain in the item; zero holes or modules were added or split off.
The private helper `uniformizer_end_unique` is proved.
The proof uses existing named dependency theorems, including the completion and
principal reduction comparison theorems, whose outstanding proofs remain their
own items. This delivery does not claim to close their transitive holes.

## No longer needed

Removed direct proof imports of `Sheaf.Paper.DerivedNakayamaResolution`,
`Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`,
`WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`,
`Mathlib.CategoryTheory.Triangulated.Pretriangulated`, and
`Mathlib.CategoryTheory.Limits.Shapes.Products`. Except for the unused product
computation theorem, their declarations are available from the necessary imports.
The temporary homology-comparison import was also removed.

`det-pe-products-derived` is no longer a direct proof dependency: a tower of zero
objects has a product without any ambient product-existence hypothesis. Its old
top-level tool-use approval was removed from the node. The general product theorem
and `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived` remain in the library; no
withdrawal or removal from the entire target import closure is claimed.
The remaining unit route, successive coefficient triangles, completeness, cones,
and first reduction, is retained. No modules are withdrawn.

## Where the brief, the DAG or earlier work was wrong

The resolution theorem uses derived tensor in the integral category, whereas the
item uses derived extension to finite coefficients. The common scalar-cone
comparison from the existing principal calculus supplies the missing interface;
no new statement is required. General existence and computation of derived
products is unnecessary for a tower already known to be zero. The existing item
docstring describes the longer strict-model proof; those strict-model results are
now imported through their existing declarations and assembled in the proof.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
