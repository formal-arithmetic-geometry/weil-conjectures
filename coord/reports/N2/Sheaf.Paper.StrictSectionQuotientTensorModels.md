## What changed

Filled `AlgebraicGeometry.ProEtale.StrictCompletionRestriction.strictSectionQuotientTensorModels`
without changing its statement or the section reduction interface. The construction now uses the
existing `strictSectionQuotientConeMaps`, rather than rebuilding its coefficient resolution.
Its component formula gives naturality, the unit equation and the successor equation.
The generator calculation reuses the proved private `RingedDerivedNative.generator_eq`
from `Sheaf.Algebra.Homology.RingedTensorComplexConstraints`, added as a private proof import.

Added proved private helpers in the item module. The tensor localization, localization
extension and singleton calculations are stated on an arbitrary ringed site of the requisite
universes, and the assembly uses them at the pro-etale site.

The helpers construct the ordinary singleton collapse
and check its value on each local pure tensor, extend the supplied HM comparison from two K-flat
factors to a K-flat first factor and an arbitrary second factor by functorial resolution, and
extend a natural comparison on K-flat representatives to the derived category by localization.
The final assembly retains the original comparison on every K-flat representative, which proves
the required `tensor_model` equation by naturality in the quotient resolution map.

Only private proof imports were added. The public import remains unchanged. The node's proof,
proof dependencies and proof origin now describe this construction. No source-library module,
public definition, declaration signature, target, or consumer is changed.

## Proved and sorry left

Closed the item's one hole:
`AlgebraicGeometry.ProEtale.StrictCompletionRestriction.strictSectionQuotientTensorModels`
(node `lem-sfb-strict-section-quotient-tensor-models`). Added zero holes. No `sorry` remains in
any delivered Lean file. The imported `strictSectionQuotientConeMaps` remains an existing proof
obligation of node `lem-sfb-strict-section-quotient-cone-maps`; this delivery does not change it.
No new public theorem statement or split-off node was introduced. The construction imposes
no flatness on the quotient and no boundedness on P. Its naturality and inverse identities
also apply to the zero quotient and the empty site. The maps chosen from the existing
cone-map existence theorem are determined by its component formula. The functorial resolutions
are auxiliary to a comparison whose value on every pair of K-flat complexes is HM.iso.inv;
the derived extension is determined by its values on all K-flat representatives.

## No longer needed

No baseline import was removed, and no module is withdrawn or globally pruned.
The proof uses Mathlib's localization API to descend the comparison.
The proof no longer directly uses `lem-pc-kflat-resolution` or chooses representatives of
derived objects: functorial resolution from the existing single-tensor comparison module
and Mathlib's localization descent replace the explicit right-fraction argument. K-flat
resolution remains necessary below that imported module.
The proof no longer directly uses `det-pe-derived-nakayama-resolution`: its coefficient-resolution
calculation is already packaged by `lem-sfb-strict-section-quotient-cone-maps`. That dependency
remains necessary below the cone-map node.
The proof does not directly invoke `lem-sfb-module-object-ringed-site-derived-comparison`:
it operates on the already supplied H and HM. The theorem and its module remain necessary as a
statement dependency and for the construction of those supplied data. The supplied t and hstep
are unnecessary for this assembly: HM's naturality fixes the tensor comparison, and naturality
of the R-algebra tower fixes the successor-unit square. Their binders are preserved verbatim.

## Where the brief, the DAG or earlier work was wrong

The original plan repeated the coefficient-resolution and cone-map construction that the sibling
node `lem-sfb-strict-section-quotient-cone-maps` already states. Reusing that statement separates
the remaining work into localization and normalization and avoids another split of the same
obligation. The unit route is unchanged; this node is below its realization nodes.

The implementation explicitly fixes the sheaf-module universe to u+1 and specifies the endpoints
of product-category tensor maps. Otherwise elaboration tries to infer endpoints by unfolding
large tensor and localization definitions. The proof keeps coefficientTotalTensor folded except
where its defining ordinary-total identification is required. The singleton comparison is
a named natural isomorphism, assembled with the identity-component uncurrying comparison,
so its naturality field can be used without unfolding the total-complex construction. The
existing generator equation identifies the prescribed summand with the sheaf pure tensor.
Proved abstract isomorphism identities perform the comparison-inverse and final-square
cancellations without unfolding the ringed tensor objects. The assembly locally keeps the
scalar-restriction construction of the coefficient module irreducible; the proof
uses its existing interface. These local attributes do not change the imported declarations.

The tensor-localization, localization descent, singleton-value and complete assembly
checks are run by the delivery tool together with its axiom probe. The implementation
abstracts the resolution comparison, chosen cone-map, representative-model
and normalized tensor witnesses behind their proved specifications, so later compatibility
fields do not reduce choice bodies.


The inverse construction for resolution comparisons and the composition and quotient of
naturality squares are proved first in arbitrary categories. The concrete assembly applies
these identities to the existing squares, avoiding repeated rewrites over tensor objects.
The singleton calculation cancels the mapped singleton isomorphism before evaluating sections.
The final source retains sequential elaboration and contains no profiling commands.

## Second reading by N2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
