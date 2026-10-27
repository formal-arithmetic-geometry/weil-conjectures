## What changed

Replaced the sole remaining hole in
`Sheaf.Paper.EtaleProEtaleCoefficientCompatibility` by a complete Lean combination of
`finiteCompactSupportDomains`, `etaleCompactScalarCoherence`, and the new normalized
scalar/site equation. The original signatures and definitions are unchanged.
Moved the existing private domain bridges and coefficient-map identification before
the main theorem so that its proof can reuse them.

The lower-bound witness is obtained for the actual scalar extension. The etale
coefficient arrow is identified with the existing compact scalar map and is invertible
by scalar coherence. The site equation makes its pro-etale counterpart invertible:
its three-factor paste equals a composite of isomorphisms, and cancellation removes
the two boundary isomorphisms. The resulting proof returns both actual invertibility
claims and the required equation. The other five theorem proofs are unchanged.

Validation: server `lcompile.py --all` compiled both modules after the explicit
isomorphism-cancellation annotation. Temporary profiler options were then removed;
the delivery runs the final compile and preflight checks.

Added `Sheaf.Paper.EtaleProEtaleCompactScalarSquare`, containing only the coherence
assertion for bounded-below inputs whose actual scalar extensions are bounded below.
This is a strict part of the argument: it assumes the scalar lower bound and supplies
neither that bound nor either coefficient arrow's invertibility. It has no field,
characteristic, torsion exponent, constructibility or finite Tor hypotheses. The
remaining task is equality of the specified normalized morphisms, especially the
intrinsic transport identification, rather than an existence or invertibility claim.

## Proved and sorry left

Closed the hole in
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.etaleProEtaleCoefficientCompatibility`
(node `lem-sp-et-proet-coefficient-compatibility`). The item module has zero remaining
`sorry` occurrences; it initially had one.

Added one hole:
`AlgebraicGeometry.ProEtale.CoefficientCompatibility.transportedCompactScalar_site_square`
in `Sheaf.Paper.EtaleProEtaleCompactScalarSquare`
(node `lem-sp-transported-compact-scalar-site-square`). Its docstring and node give the
source, complete mate-pasting argument and precise normalization that remain to be
formalized.

This is a decomposition: one upper hole closed and one strictly smaller coherence
hole added, for net zero holes closed. All other used declarations retain their
existing proofs and holes. No hole is hidden inside a definition or a private helper.

Edge cases checked in the new statement: zero objects and empty schemes give the
same zero-map equation; identity coefficient maps use the same unit-normalized
comparisons on both routes; maps to the zero ring reduce to the zero category.
A nonflat map such as Z/ell^2 to Z/ell is allowed only on inputs for which the
actual scalar extension is bounded below. No preservation of D+ by arbitrary scalar
extension is assumed.

## No longer needed

Removed the redundant direct proof import `Sheaf.Paper.EtaleCompactScalarCoherence`:
the new square module publicly imports it for `compactScalarMap`, so the same
statements remain available to the item proof. No mathematical module is withdrawn.

The main theorem no longer needs `reductionDirectImage_isIso`
(`det-sp-reduction-direct-image`) or reflection of inverses through the fully faithful
site comparison (`thm-weil-pbc-site-comparison`). It instead derives pro-etale
invertibility from the existing etale coefficient isomorphism. Their modules remain
publicly imported for the existing interface and constructions; this is not a claim
that these modules are globally pruned.

Removed the direct parent proof dependency on `lem-sp-finite-coefficient-input-models`:
`finiteCompactSupportDomains` already supplies the needed scalar lower bound. Its
transitive dependency remains needed by that theorem. The parent directly uses the
new square instead of `lem-sfb-etale-proetale-scalar-mate`,
`lem-sp-open-scalar-site-coherence`, and
`lem-weil-pbc-comparison-direct-image-canonical-mate`. Proper and open mate theory
is retained in the new child's proof plan; it is not declared globally unnecessary.
No import or node belonging to the sum, refinement, composition or counit arguments
is pruned. No source-library declaration or module is removed.

## Where the brief, the DAG or earlier work was wrong

No statement dispute or interface defect was found. The planned use of intrinsic
reduction invertibility followed by full-faithfulness reflection is longer than
needed once `etaleCompactScalarCoherence` is available. Its first clause gives the
etale isomorphism directly, and the site equation then gives the pro-etale one.
The node now records that route. The difficult glue is the equality of the actual
intrinsic transport with proper/open fixed-coordinate mate pasting, isolated in the
new statement without claiming that the endpoint isomorphisms identify maps by
themselves. The unit route is preserved.

## New nodes

`lem-sp-transported-compact-scalar-site-square`, in
`dag/nodes/sec-smooth-purity/lem-sp-transported-compact-scalar-site-square.json`,
states the site/coefficient equality alone, for finite rings with only the two D+
hypotheses. It records the proper mate square, the open left-mate cube, and the
unit/counit-normalized intrinsic realization argument. Mathlib searches returned
generic mates and sheaf comparisons, not this normalized equation. Blueprint-wide
search for scalar/site comparisons found no imported node stating this particular
transport equality separately from the original conjunction. No change record is
needed: no existing definition or statement was changed.

## Second reading by K2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
