## What changed

Proved `AlgebraicGeometry.ProEtale.sp_coefficient_towers_abelian_axioms` without
changing its statement. Construct the vertical product topology on ℕ × T.ProEt,
bundle the actual varying coefficient presheaf as a ring sheaf, and identify the
existing full subcategory with its sheaves of modules. The equivalence fixes the
underlying presheaves and maps. Transfer finite products and apply Mathlib's
`abelianOfEquivalence`, then extract its five axioms.

Added the proof-only import `Sheaf.CategoryTheory.DiagramSiteTopology`.
Generalized that unclaimed module's vertical topology and sheaf criterion to
independent universes and a direct index category; every existing public signature
is preserved as a specialization. All construction and criterion proofs are complete.
The original sheaf- and module-equivalence consumers compile unchanged.

Change record: `coord/changes/D5-vertical-diagram-site-universes.md`.
Updated the item's node to record the direct vertical-site route for the axioms.
The full coefficient-tower/derived-reduction theorem and its proof plan are unchanged.

## Proved and sorry left

Closed one of the two original holes:
`AlgebraicGeometry.ProEtale.sp_coefficient_towers_abelian_axioms`
(node `det-sp-coefficient-towers-abelian`).

The only remaining hole is
`AlgebraicGeometry.ProEtale.sp_coefficient_towers_abelian`
(node `det-sp-coefficient-towers-abelian`). It still needs the normalized
uncurrying equivalence with strict systems, Grothendieck/exact evaluation data,
and the canonical ordinary and derived reductions and their compatibility.
No holes added, no split-offs, and no holes in definitions. The support module has zero holes.
This is a partial proof delivery, not a decomposition.

The current server compiler checked both delivered modules and all three unchanged realization
consumers (the sheaf equivalence, module equivalence, and realization theorem). `#print axioms sp_coefficient_towers_abelian_axioms` reports exactly
`propext`, `Classical.choice`, and `Quot.sound`.

## No longer needed

None. No imports removed. The direct abelian-axioms proof needs only the
vertical-topology criterion and Mathlib module-sheaf abelianness and equivalence
transport. The other declared dependencies remain part of the unchanged open
main theorem's plan; this delivery does not prune that argument or any unit step.

## Where the brief, the DAG or earlier work was wrong

The product-site declaration available from the DAG had a same-universe,
opposite-index API. The scheme site has object universe t+1 while the index is ℕ,
and the module universe is max u (t+1), so that API does not fit the actual tower
presheaf. The generalized construction removes only these artificial API
restrictions. Empty sites, trivial coefficient rings, and index identities need
no exceptions: the equivalence retains every object and morphism and changes
only proof fields. The underlying covering-sieve construction is unchanged.

## Second reading by D5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
