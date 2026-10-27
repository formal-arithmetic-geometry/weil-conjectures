## What changed

Filled `AlgebraicGeometry.ProEtale.InternalCompletionTransport.ordinary_uniformizer_scalar_comparison`
in `Sheaf.SixFunctors.ProEtale.OrdinaryUniformizerScalarComparison`.
The proof fixes the canonical coefficient isomorphism, constructs its compatible first-quotient
isomorphism, and checks the scalar equation on sections. Private proved helpers normalize the
constant section through sheafification, monoidal inverse image, section-ring reconstruction,
and the equivalence of sites. The internal left-unitor action and the ordinary right-unitor
pure-tensor formula identify the two scalar maps. The public statement and existing public
imports are preserved. Updated the item's proof route and dependencies in its DAG node.

## Proved and sorry left

Closed the one original hole in
`AlgebraicGeometry.ProEtale.InternalCompletionTransport.ordinary_uniformizer_scalar_comparison`.
Added zero holes. No `sorry` remains in the item or in any added declaration. No split-off
statements or modules. The complete proof compiled with `lcompile.py` in 45.7 seconds. Its `#print axioms`
output is exactly `propext`, `Classical.choice`, and `Quot.sound`. Profiler and lowered
diagnostic limits were removed before delivery; the delivery tool revalidates the final file.

## No longer needed

No module or node is withdrawn. The original declared dependencies remain needed for their
coefficient constructions, regular-action expression, quotient comparison and tensor APIs.
The proof does not require any new intermediate obligation or any extension of the nine-step
chain above this item. No changes to source-library declarations or to other existing modules.

## Where the brief, the DAG or earlier work was wrong

The item initially occurred only at its rework quarantine path; the archived module and its
attachment were preserved and used as the starting source. The live source has since been
restored by synchronization. The mathematical statement and planned route are valid.
The constant and continuous coefficient maps and the required tensor formulas were already
proved; making their normalizations explicit closes the remaining ordinary scalar step.

## Second reading by T4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
