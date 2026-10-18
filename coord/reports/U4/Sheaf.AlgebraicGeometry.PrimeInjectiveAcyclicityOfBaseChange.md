## What changed

Proved `AlgebraicGeometry.Etale.hasAllPrimeInjectiveAcyclicity_of_hasTorsionAbelianBaseChange`
in `Sheaf.AlgebraicGeometry.PrimeInjectiveAcyclicityOfBaseChange`, preserving its signature
and the unit's PBC-to-IA argument. No definitions or statements changed.

The proof establishes torsion using the existing torsion characterizations, transfers
injectivity across `constantRing_moduleSheaf_equivalence`, applies
`isZero_higherDirectImage_of_injective_module`, and transports vanishing through exact
pullback, the specified exchange isomorphism, and the pullback/single-functor comparison.
It handles every positive integer degree by conversion to a positive natural degree.

Added proof-only imports of
`WeilConjectures.AlgebraicGeometry.ConstantRingModuleSheafEquivalence` and
`WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations`. Updated the existing
node's proof and dependencies, and corrected its stale Lean signature record to the
unchanged actual declaration. No consumer adaptations or change records are necessary.

The sandbox module compiled cleanly through `lcompile.py` (8.2 seconds).
Searches with LeanFinder, Loogle and grep found generic derived-injective vanishing and
`Functor.map_isZero`, but no shorter theorem for this abelian prime-field statement.
The source library's analogous `HasTorsionBaseChange.hasInjectiveAcyclicity` concerns
module-valued base change, so its method is reused rather than its different hypothesis.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.Etale.hasAllPrimeInjectiveAcyclicity_of_hasTorsionAbelianBaseChange`
(node `lem-weil-pbc-property-implies-acyclicity`).

Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean module.
The proof uses the project declarations as intended by stage 3; this does not claim
that every dependency of those declarations has already been proved.

## No longer needed

Removed the proof dependency
`lem-weil-pbc-left-exact-injective-resolution-degree-zero`: the positive cohomology
vanishing theorem directly supplies all degrees needed for IA, and degree zero is never used.
The unit's forward implication and its required nodes remain in place.

Removed these nine direct proof imports:

- `Sheaf.AlgebraicGeometry.DerivedCategories` (retired re-export wrapper).
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageExact` (the exactness instances
  already accompany the pullback functor; its bundled theorem is unnecessary).
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves` (no additional declaration needed).
- `WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor` (the required
  comparison API is already publicly available through the statement imports).
- `WeilConjectures.SixFunctors.BaseChange.Derived` (already a public dependency of PBC).
- `WeilConjectures.SixFunctors.BaseChange.Square` (already available with PBC).
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs` (already available with PBC).
- `Sheaf.AlgebraicGeometry.ChosenCartesianSquare` (the statement supplies IsPullback;
  no additional chosen pullback identification is needed).
- `WeilConjectures.AlgebraicGeometry.DerivedCategories` (no declaration of this module
  is needed beyond the derived-category API already available).

These are removals of direct imports, not claims that their modules disappear from every
other target dependency. The conceptual exactness and derived-category dependencies are
retained in the DAG because those properties are used by the comparison APIs.

## Where the brief, the DAG or earlier work was wrong

The planned acyclicity lemma uses `SheafOfModules`, whereas the assigned statement uses
module-valued `Sheaf`. The existing constant-ring module-sheaf equivalence supplies the
necessary injectivity and underlying-abelian-sheaf comparison, with no new lemma.
The original DAG omitted this interface bridge and the torsion-predicate comparison;
both existing nodes are now recorded in the proof dependencies.

The node's Lean record still named `HasAllPrimeInjectiveAcyclicity`; the actual module
already used `HasAllPrimeAbelianInjectiveAcyclicity`. Only the record was corrected.
The original prose's degree-zero identification is true but superfluous to this proof.
The proof preserves the properness assumption, all universes, all base changes and every
prime. The empty scheme needs no exception; nonpositive degrees are excluded by the
original IA conclusion, and primality supplies the finite nonzero coefficient ring.

## Second reading by U4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
