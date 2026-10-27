## What changed

Proved `AlgebraicGeometry.ProEtale.ScalarQuotientChain.scalar_quotient_chain_squares`
in `Sheaf.Paper.IsomorphismScalarQuotientChainSquares`. Its hypotheses and conclusion are unchanged up to definitional equality.
The private helpers construct reassociation by uniqueness of normalized scalar-extension
adjoints and transport this adjunction across the corresponding-object module equivalence.
They compute the forward and inverse tensor formulas. The right quotient and transition
maps come from transposed extension units; conjugating them by the finite comparisons
gives the left maps. The assumed normalization of the upper comparison and the coefficient
commuting squares give precisely the requested left formulas. Naturality and lifting to
complexes supply the chain-map laws; inverse cancellation gives both whole-map squares.

The module uses the two existing statement dependencies and a private Mathlib adjoint
uniqueness import. The functor abbreviations are normalized definitionally, with explicit
result types, and successor indices in Tower, Transport and TransitionFormulas avoid costly unfolding.
The final theorem uses the same successor spelling and explicit restriction universes. See
`coord/changes/Q7-scalar-quotient-functor-normalization.md`. No other module is changed.
The node's proof, proof_deps and proof_origin describe this route.

## Proved and sorry left

Closed: `AlgebraicGeometry.ProEtale.ScalarQuotientChain.scalar_quotient_chain_squares`
(blueprint `lem-weil-isomorphism-scalar-quotient-chain-squares`), 1 of 1 original holes.
Added: 0 holes. Remaining in the delivery: 0 holes. Every private helper is proved;
there are no new public intermediate statements or hollow definitions.
The proof continues to depend on the recorded site-equivalence theorem; this does not
claim to close holes in its module or in the targets' entire import closure.

## No longer needed

Removed imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`;
- `Mathlib.Algebra.Homology.BifunctorShift`;
- `Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification`;
- `WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension`;
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal`.

The proof no longer directly needs proof-dependency nodes
`def-pc-tensor-complex-sheaves`, `def-pur-sheaf-tensor-product`,
`def-weil-presheaf-modules-sheafification`,
`lem-pc-sites-module-sheafification-bilinear-extension`, or
`lem-pc-sites-sheaf-tensor-bilinear-universal`. Reassociation and the maps use the
already constructed normalized adjunction instead of repeating the sheaf bilinear
extension argument. Accordingly the obsolete tool_uses approvals for the tensor and
bilinear lemmas are removed; the site-equivalence approval stays. Definitions that are
statement dependencies remain in stmt_deps, and the unit route is retained. No module
or declaration is withdrawn, including any declaration in WeilConjectures. These
modules can remain needed elsewhere; this is pruning only this node's proof route.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement was disputed or weakened. The planned repeated bilinear
extension construction was unnecessary given the existing normalized scalar adjunction.
Whole-functor reduction and index addition caused substantial elaboration cost; the
change record describes definitionally equal normalizations and their consumer scan.

## Second reading by Q7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
