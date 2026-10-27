## What changed

Proved `AlgebraicGeometry.ProEtale.PurityTransport.rootComparison_existsUnique`
in `Sheaf.SecSmoothPurity.TransportRoot`, preserving its complete statement and
all four coordinate definitions. The proof identifies the underlying kernel
presheaf sectionwise with `rootsOfUnityPresheaf`, sheafifies this natural
isomorphism, and establishes normalization and uniqueness by the universal
property of sheafification. Updated the existing node's proof, proof dependencies
and proof origin to describe this argument. No imports or public interfaces changed.
The required `lcompile.py` single-file check passed without errors or warnings
in 6.0 seconds; delivery preflight supplies the independent axiom probe.

## Proved and sorry left

Closed the single original hole:
`AlgebraicGeometry.ProEtale.PurityTransport.rootComparison_existsUnique`
(node `def-pur-transport-root-coordinates`). No holes remain in the item and
no holes were added or split off. The proof uses the already proved
`existsUnique_proEtaleRootsOfUnitySections` and Mathlib's sheafification API.

## No longer needed

None. No imports removed, no modules withdrawn and no declared dependencies
pruned. The previous node had an empty proof and empty proof dependencies.
The existing `TransportCoefficients` public import is still needed by the
coordinate definitions. No unit step is bypassed.

## Where the brief, the DAG or earlier work was wrong

The existing node had no proof steps for its existence-and-uniqueness theorem;
these are now recorded. No mathematical or statement repair was necessary.
The proof works for every natural exponent, including zero and one, and for
empty schemes: it uses kernel section equivalences and the sheafification
universal property without division, positivity, or invertibility assumptions.

## Second reading by Q4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
