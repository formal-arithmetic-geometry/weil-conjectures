## What changed

The source module retains both declaration signatures, its existing projection-associativity
proof, and its public import. The composition family is the explicit product-graph
`sfGraphCompactSupportCompIso` on the chosen compactifications, transported along `w`.
Projection compatibility is isolated as a separate, strictly smaller result; its proof outline
cancels the inverse projections in `sfEtaleCompactProjectionInverse_composition`. Base change
is proved for that same
family, with quasi-compactness only for the primed maps.

Three new Sheaf modules provide exact exchange pasting, the projection subproblem, and
the proved base-change equation for the
fixed graph compositor. The latter constructs the proper/open graph diagram, identifies
its word with the compositor, pulls it back factorwise, compares it with the primed chosen
diagram, and transports exact inverse image to left-derived inverse image. Its exchange
transport reuses the proved private helper of UnboundedEtaleCompactSupportComparisons.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso`.
The existing `projectionMapAssociativity` proof is preserved.

Added one hole, in the public theorem
`AlgebraicGeometry.Etale.sfGraphCompactSupportCompIso_projection`
(node `lem-r9-graph-compositor-projection`). This is a decomposition, with net zero
holes closed. It asserts only the projection clause for the fixed constructed compositor;
the separate base-change clause is proved here by an explicit graph and exchange calculation.
No other delivery declaration contains `sorry`.

Proved new public declarations:
`AlgebraicGeometry.Etale.sfExactExchangePasting` and
`AlgebraicGeometry.Etale.sfGraphCompactSupportCompIso_baseChange`.
The projection subproblem remains because converting the existing inverse equation between
generic derived tensor and monoidal notation repeatedly triggered expensive hidden-instance
and functor-object conversions. The categorical cancellation itself was checked separately.

## No longer needed

No upstream declaration or module is withdrawn. No public import is removed.
The proof follows the existing graph route; intermediate dependency imports are private.
The existential compact-support composition theorem is not used to choose isomorphism data.
The copied proof of exact exchange transport was removed in favor of its existing proved
private helper, imported with `import all`.

## Where the brief, the DAG or earlier work was wrong

The plan is mathematically usable with its original hypotheses. The existing unbounded
compact-support comparison module's top-level coherence theorem requires quasi-compactness
of the original maps and Noetherian schemes, so it cannot directly prove this item.
Its private exact-exchange transport helper has neither restriction and is reused.
The inverse projection identity uses generic derived tensor notation, while the public
statement uses monoidal notation; the coefficient braiding instances are definitionally
equal but require explicit congruence to avoid expensive expansion of derived monoidal data.

## New nodes

`lem-r9-exact-exchange-pasting` records identity normalization and proper/open composition
pasting for the specified exact-derived exchange maps. Its proof uses adjunction mates,
canonical pullback compositors, and open compositor normalization.

`lem-r9-graph-compositor-base-change` records compatibility of the fixed explicit graph
compositor with the specified exchange maps, including graph shrinking, diagram independence,
and the transport to the existing left-derived-pullback API.

`lem-r9-graph-compositor-projection` records only projection compatibility of the fixed
graph compositor. Its docstring gives cancellation of the existing inverse projection
identity as a complete proof outline. Base-change compatibility is not assumed in it.

## Second reading by R9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
