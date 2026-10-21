## What changed

Filled `WeilConjectures.complete_residue_cohomology_bounds` without changing its
signature or public imports. The proof follows the current four-step DAG route:
test the residue Tor predicate on the tensor unit, use
`strictDvrReductionTriangles`, induct on the quotient level, and apply
`AlgebraicGeometry.Scheme.ProEt.bounded_epimorphic_top_derivedLimit`.

The proof includes two proved private helpers. `tor_cohomology_bounds` computes
tensoring with the degree-zero coefficient ring by the ordinary complex right
unitor. `reduction_transition_eq` identifies the legacy and unrestricted chain
transitions by their unique pure-tensor characterization. The main proof compares
the strict-triangle K-flat model with the completeness model through a common
K-flat roof and `unrestrictedReductionTowerWellDefined`; all transition squares
are explicit. It transports both vanishing and top epimorphy, rather than merely
identifying the objects of the two towers.

The node's proof and proof dependencies now record the identity pullback,
K-flat resolution, exact scalar restriction, and compatible tower comparison
used by the Lean assembly. The unit route is unchanged.

Validation: `lcompile.py` compiled the final module cleanly in 14.1 seconds.
The original theorem signature and all public imports are verbatim unchanged;
all delivered Lean lines satisfy the 100-character limit. Private coefficient instances pin the site and module universes without changing any public signature.

## Proved and sorry left

Closed: `WeilConjectures.complete_residue_cohomology_bounds`
(node `lem-sf-complete-residue-cohomology-bounds`), the only original hole.
Added: none. Remaining in delivered Lean files: none. This is a proof from the
existing declared dependencies, with no new split statements. In particular,
`WeilConjectures.strictDvrReductionTriangles` remains an existing dependency
whose proof is outside this packet. No claim is made that all transitive axioms
of the project have been eliminated.

## No longer needed

Removed the following private imports from the item, because their content is
encapsulated by the two designated dependencies or unused by this assembly:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.AlgebraicGeometry.ProEtaleMilnorSequence`
- `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`
- `Sheaf.AlgebraicGeometry.ProEtaleMilnorEpimorphic`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.AlgebraicGeometry.CoefficientProEtaleTorAmplitude`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`

No previously declared proof dependency was bypassed. The direct Milnor/product
nodes remain dependencies of the bounded-limit theorem; the coefficient
exactness and K-flat tensor nodes remain dependencies of the strict DVR triangle
theorem. Consequently this packet does not claim those modules are globally
pruned and withdraws no module or declaration.

## Where the brief, the DAG or earlier work was wrong

The module docstring still spells out the original seven paragraphs, while the
current DAG groups the coefficient construction and the Milnor argument into two
separately stated results. Both describe the same argument. The assembly must
also account for the possibly different K-flat model in the completeness
witness; a termwise isomorphism alone would not identify the quotient tower.
This packet supplies the transition-compatible comparison explicitly.

The residue ring is finite by `Padic.finite_coefficientExtensionRing` at exponent
one, which supplies the hypothesis of the existing identity pullback theorem.
No condition on constructibility, local constancy, residue characteristic, or
cohomology finiteness was added. Empty schemes, zero complexes, singleton
intervals, and negative interval endpoints use the same argument.

## Second reading by J6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
