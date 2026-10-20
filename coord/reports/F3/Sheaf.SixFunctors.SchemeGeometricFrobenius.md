## What changed

Proved `WeilConjectures.PurityFiniteSetting.schemeGeometricFrobenius_factorization`
by checking the two projections of the chosen base change. The coefficient-projection
calculation uses the arithmetic Frobenius power formula on the field. Composing with
the inverse coefficient action gives the geometric factorization.

Proved `WeilConjectures.PurityFiniteSetting.schemeGeometricFrobenius_squares`
from the existing Cartesian Galois-square theorem, Frobenius naturality, universal
homeomorphism of absolute Frobenius, and the stated etale invariance theorem.
The absolute-Frobenius naturality calculation is a proved private helper.
All existing public signatures and definition bodies are unchanged.
The node records the shorter projection argument for the factorization.

## Proved and sorry left

Closed 2 of the item's 3 original holes:
`WeilConjectures.PurityFiniteSetting.schemeGeometricFrobenius_factorization` and
`WeilConjectures.PurityFiniteSetting.schemeGeometricFrobenius_squares`.

One original hole remains, with its original statement, source, proof in words and node:
`WeilConjectures.PurityFiniteSetting.schemeGeometricFrobenius_naturality`
(`def-pur-scheme-geometric-frobenius`). No holes or new declarations with holes are added.
This is a partial proof delivery, not a claim that naturality is proved.
The item compiles cleanly through the prescribed launcher (11 seconds in the verified run).

## No longer needed

The factorization does not need `lem-weil-pbc-fibre-product-affine-spectra`:
the projections of the chosen pullback determine both composites directly. Removed
that node from this node's proof dependencies and from its factorization proof step.
Its standalone module is not imported by this item. No existing imports are removed;
the other dependencies remain relevant to the definitions, the proved square theorem,
or the retained naturality proof plan.

## Where the brief, the DAG or earlier work was wrong

The affine tensor-product calculation planned for factorization is unnecessary.
Naturality requires an explicit associativity law for the normalized composition
comparisons. Several attempted private proofs incurred expensive definitional equality
through the module-category interfaces; none is included in this delivery.
An exploratory statement about arbitrary trivializations was rejected because the
normalization hypotheses are essential. All exploratory modules and added holes were
removed from the delivery. The original naturality hole is retained rather than
replaced by a restatement or an unverified proof.

## Second reading by F3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
