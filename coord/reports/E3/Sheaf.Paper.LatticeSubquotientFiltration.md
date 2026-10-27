## What changed

Completed `AlgebraicGeometry.ProEtale.exists_latticeSubquotientFiltration` in
`Sheaf.Paper.LatticeSubquotientFiltration`. Finite type over the coefficient base field
supplies the Noetherian structures on S and X. The existing abstract assembly helper
then applies to `exists_orderedSpectralLattices`, with the identical spectral coefficient
rings, inclusion and lattice adjoints. The assembly retains the existing ordered
extension filtration and scalar compatibility comparisons, so the DAG proof route and
the integral-models unit route are unchanged. All public statements, definitions and
imports are unchanged. The helper application is first inferred from the ordered-lattice
hypothesis, then matched to the goal; this preserves its coefficient instance terms and
avoids the kernel timeout caused by inferring those structures from the final goal.

Searches: LeanFinder for a lisse lattice filtration returned adic completion and ideal
filtration declarations, not this sheaf assertion; Loogle for `"Sheaf", "lattice"`
returned submodule lattice structures; Mathlib grep for lisse/lattice filtrations
returned ideal and probability filtrations. Searches of both project library roots
found the existing ordered-lattice and assembly declarations used here.

## Proved and sorry left

Closed 1 of 1 item holes:
`AlgebraicGeometry.ProEtale.exists_latticeSubquotientFiltration`
(node `lem-sfb-lattice-subquotient-filtration`). No sorry remains in the item module;
no hole is added or split off. The proof uses the already stated
`AlgebraicGeometry.ProEtale.exists_orderedSpectralLattices`; its existing sorry remains
in its own module and is not part of this delivery.

## No longer needed

None. All three private proof imports are used by the retained argument:
`Sheaf.Paper.OrderedSpectralLattices`, `Sheaf.Paper.LocallyClosedOrderedFiltration`,
and `Sheaf.Paper.CondensedLocallyClosedScalarExtension`. No node, module or import is
pruned. The four recorded proof dependencies are still exactly those used.

## Where the brief, the DAG or earlier work was wrong

The earlier delivery had already proved both assembly helpers; the remaining
step was their specialization to the canonical spectral coefficient construction.
The argument imposes no positive-rank, nonempty-stratum or strict-filtration assumption,
so it preserves the empty and zero cases of the recorded assertions.

During implementation, inferring the helper parameters from the goal repeatedly timed
out in kernel conversion of the lattice hypothesis. Expression comparison found 372
occurrences of the coefficient-object abbreviation versus its expanded functor-object
form. Inferring the helper parameters from the ordered-lattice hypothesis first resolved
this without changing a definition, statement, import, transparency setting or time limit.
All diagnostic tactics and profiling options were removed. The final module compiled
cleanly through `lcompile.py` in 9.6 seconds, with no errors or warnings.

## Second reading by E3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
