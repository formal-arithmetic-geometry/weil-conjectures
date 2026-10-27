## What changed

Proved `AlgebraicGeometry.Scheme.coefficientSurjectiveRestriction_constructible` in
`Sheaf.Paper.CoefficientSurjectiveRestrictionConstructible` without changing its statement
or public imports. All additional comparisons are private and proved in this module.

The proof identifies intrinsic restriction with fixed-scalar restriction sectionwise by
naturality of the constant-ring sheafification unit. Restriction commutes with the Kan
extension and sheafification that define the stratum pullback. On each slice,
`constantCommuteCompose` restricts the constant trivialization. Surjectivity preserves the
finite generating set and Noetherianity gives finite presentation. The same strata and
covering sieves therefore work over the source ring. Finally the exact derived restriction
cohomology comparison identifies this sheaf with the cohomology in the conclusion.

Proof imports: Mathlib Kan-extension preservation, site adjunctions, Noetherian modules,
and filtered colimits of modules. Explicit private sheafification instances avoid expensive
general instance search on slice sites; the general essentially-small instance is disabled
only while elaborating the private sheafification instance and the final theorem.
The standard derived category is locally irreducible. No shared interface was changed.

Updated the item's node proof, proof dependencies and proof origin to match this argument.
The first complete proof compiled remotely in 5.9 seconds. Its `#print axioms` output was
exactly `propext`, `Classical.choice`, and `Quot.sound`; there was no `sorryAx`.
The temporary axiom-print command was removed for delivery.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.Scheme.coefficientSurjectiveRestriction_constructible`
(node `lem-sfb-coefficient-surjective-restriction-constructible`).

Zero holes remain; zero holes added; zero statements split off. This is a complete proof,
including all private comparisons and the finite-presentation argument, not a decomposition.
The proof requires neither a nonzero coefficient ring nor a nonempty scheme, and keeps the
independent coefficient universe and the unbounded derived input.

## No longer needed

The following planned proof dependencies are not used and were removed from the item's
`proof_deps` and proof-step `uses`:

- `def-weil-pbc-proetale-operations`
  (`Sheaf.AlgebraicGeometry.ProEtaleConstantRingOperations`): direct use of the fixed-scalar
  pullback's Kan-extension/sheafification construction supplies the comparison.
- `def-sfb-site-derived-constant-module-functor`
  (`Sheaf.CategoryTheory.CommutativeSiteDerivedConstantModuleFunctor`): the ordinary
  Mathlib `constantCommuteCompose` comparison suffices for the local constant models;
  derived constant realization is unnecessary.

Neither was directly imported in the original item. Both original public imports are
retained, so this does not claim those modules disappear from the transitive import closure.
No existing Lean module is withdrawn. The redundant new proof import
`Mathlib.CategoryTheory.Functor.KanExtension.Adjunction` was removed because
`Mathlib.CategoryTheory.Functor.KanExtension.Preserves` already imports it.

## Where the brief, the DAG or earlier work was wrong

The statement and its mathematical plan were correct. The generic pro-etale operations and
derived constant realization dependencies were unnecessary: Mathlib's ordinary constant
sheaf, Kan extension and exact derived functor APIs close every step. The node now explicitly
records `lem-weil-pbc-flat-ringed-ideal-complete-equivalence`, whose proved
`siteRestrictScalars_exact` supplies exactness. No unit route, statement or definition was
changed. No new node or change record is needed.

## Second reading by G2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
