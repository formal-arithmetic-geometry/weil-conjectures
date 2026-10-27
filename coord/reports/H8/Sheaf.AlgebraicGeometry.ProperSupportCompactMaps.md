## What changed

Proved the four remaining theorems in
`Sheaf.AlgebraicGeometry.ProperSupportCompactMaps`. All existing public declarations,
signatures, attributes, definitions, and public imports are unchanged. Added only private,
proved helpers and proof imports; updated the module's own DAG node
`def-pur-proper-support-compact-maps` to record the implemented argument.

On each site the restriction isomorphism is direct-image composition followed by the
open direct-image counit. The quotient-composition equation verifies its prescribed
normalization, and cancellation of the pulled-back epic quotient proves uniqueness.

For etale extension, apply the finite/open comparison to the cartesian square with
upper arrow `id_Z`, left arrow `i`, right arrow `i ≫ c.i`, and bottom arrow `c.i`.
The right arrow is closed, hence finite. This gives an ordinary extension isomorphism.
The pro-etale isomorphism follows by transporting it through the existing comparisons
for supported coefficients and open extension by zero. After deriving, the target is
in the essential image of the fully faithful open extension functor. Its counit is
therefore invertible, proving invertibility of the specified adjoint transpose.
This works for arbitrary coefficient complexes, including unbounded ones.

The final single-file remote compile completed cleanly in 19.0 seconds. No other existing
module was changed. All added proof imports were checked: none is publicly available
through the other imports. The new proof dependencies were checked for a path back to
the item; none exists.

## Proved and sorry left

Closed 4 original holes, all attached to `def-pur-proper-support-compact-maps`:

- `AlgebraicGeometry.Etale.compactSupportCoefficientRestriction_existsUnique`
- `AlgebraicGeometry.Etale.compactSupportCoefficientExtension_isIso`
- `AlgebraicGeometry.ProEtale.compactSupportCoefficientRestriction_existsUnique`
- `AlgebraicGeometry.ProEtale.compactSupportCoefficientExtension_isIso`

Holes added: 0. Holes remaining in the item: 0. No split-off statements or new nodes.
Imported library declarations retain their existing proof status.

## No longer needed

No existing imports, modules, or DAG dependencies are removed or withdrawn.
The direct local-cover/termwise proof suggested in the extension docstrings is
unnecessary: finite/open comparison and the essential-image counit criterion give
the required isomorphisms. No new locality, stalk, or derived-descent lemmas are needed.
The blueprint unit's statement and steps remain intact.

## Where the brief, the DAG or earlier work was wrong

No statement error was found. The item's node had no proof steps or proof dependencies;
it now records the proof actually implemented. The shorter finite/open comparison route
reuses the existing source theorem, and its pro-etale transport uses only the stated
locally Noetherian hypotheses. The normalized chosen isomorphisms and all constructions
using them are preserved. The empty support, zero coefficients, identity open immersion,
and arbitrary cohomological degrees require no exclusions in these functorial arguments.

## Second reading by H8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
