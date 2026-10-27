## What changed

Filled `AlgebraicGeometry.ProEtale.embeddedIntegralResidueSquare` in
`Sheaf.Paper.EmbeddedIntegralResidueSquare`, preserving its signature and existing docstring.
The proof follows the existing two-step DAG plan. Private proved helpers reconstruct a
ring-sheaf map from its internal monoid map, identify one-point continuous functions with
scalars, express naturality of constant sheafification, and transport maximal ideals.
The evaluated ring isomorphism is a private irreducible definition so that quotient
checking does not expand the sheaf construction. The fully proved private helper
`coefficientSquares` works with abstract topological local rings: this keeps Lean from
rechecking the large concrete coefficient instances throughout the sheaf argument.
The public theorem supplies the two actual rings and their maximal-ideal identifications. Evaluating the given isomorphism
produces an ordinary ring isomorphism. Its constant sheafification gives `d`. Naturality for
the map from each profinite set to the one-point set proves the scalar square.
The recorded DVR properties identify the spectral first ideal with its maximal ideal;
`IsLocalRing.map_ringEquiv_maximalIdeal` and `Ideal.quotientEquiv` then construct `r`.
Functoriality of constant sheafification proves the residue square.

Added private proof imports of `Mathlib.RingTheory.Ideal.Quotient.Operations` and
`Mathlib.RingTheory.LocalRing.RingHom.Basic`.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.embeddedIntegralResidueSquare`
(node `lem-sfb-embedded-integral-residue-square`).
No holes added, no split-off statements, and no `sorry` remains in the delivered module.
The complete module compiled without errors or warnings in 16.8 seconds through `lcompile.py`.

## No longer needed

None. Both original public imports remain needed by the statement. All three declared
proof dependencies remain used: the two coefficient presentations and
`lem-weil-l-adic-extension-integers-dvr`. No module or node is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No statement or definition repair was needed. The existing plan can be formalized directly
using the library's sheaf-to-presheaf multiplication formula, the constant-sheaf adjunction,
and Mathlib's local-ring and quotient-equivalence APIs. No new nodes are needed.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
