## What changed

Filled `WeilConjectures.supported_tor_reduction_propagation` without changing its
signature or any public definition. Added proved private helpers for interval transport,
residue specialization, full-subcategory adjunction restriction, the finite exceptional
estimate, and integral triangulation. The restricted adjunctions use the original unit
and counit components, and the restricted setup uses the original boundary. Conditional
zero and invertible-unit assertions follow from fullness.

The finite estimate uses inverse rotation, interval enlargement, and the quantitative
shift/common-interval extension clauses of `finite_ctf_isTriangulated`. The supplied
reduction isomorphisms transfer the four input bounds and exceptional bound at every
level. Integral triangulation uses the exact structure already specified by
`scalarReductionDerivedExistence`; it requires no auxiliary finite-field datum.

Updated the existing node's proof, proof dependencies, proof origin and obsolete tool
entries. Updated the theorem's proof explanation to match. Removed the old transparency
override. No public imports, signatures, definitions, or consumer modules changed.

## Proved and sorry left

Closed 1 hole: `WeilConjectures.supported_tor_reduction_propagation`
(node `lem-sf-supported-tor-reduction-propagation`). Added 0 holes; split off 0.
There are no remaining `sorry` declarations in the delivered module. Every new private
helper is proved. Server single-file compilation passed; the final delivery tool also
checks compilation and declaration axioms.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.ProEtaleTorIntervalTriangle` and
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`.

The proof does not need `lem-weil-proetale-tor-interval-triangle`: the existing intrinsic
finite triangulation theorem already supplies the common-interval extension result,
so interval enlargement avoids a bridge to the coefficient-sized site presentation.
The proof does not need `lem-pur-derived-change-of-rings`: exactness is already part of
the specified scalar reduction construction, while the node currently attaches an
ordinary-module change-of-rings theorem. Removed both unused tool approvals from this
node. These modules remain available to their other consumers; no module is withdrawn.
All other declared dependencies are retained, and the unit route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The original plan's two extra generic tools are unnecessary given the current declared
interfaces. In particular, the interval-triangle node now uses a coefficient-sized site
presentation, whereas this item's amplitude predicate uses the original intrinsic site;
the finite triangulation theorem matches exactly. The integral scalar reduction's
existence specification already includes its exact triangulated structure. No statement
repair was needed. The proof handles level n=0, N=0, zero objects, and empty closed/open
parts without additional hypotheses; the residue module is never assumed flat.

## Second reading by R4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
