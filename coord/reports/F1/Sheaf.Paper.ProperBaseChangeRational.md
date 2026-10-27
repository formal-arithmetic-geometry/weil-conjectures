## What changed

Completed the two remaining proofs in `Sheaf.Paper.ProperBaseChangeRational` without changing
any public signature. The existing preservation abbreviation now establishes the finiteness
coefficient class once before applying the same preservation theorem; its type and claim
are unchanged. Private helpers transport the canonical projection map
through coefficient isomorphisms, scalar extension and isomorphisms of its two inputs.
For finite coefficients, essential surjectivity of integral rationalization provides integral
models. The integral proper projection theorem, tensor/pullback closure and the canonical
coefficient/projection square then prove the rational projection formula. For algebraic-closure
coefficients, descend both objects to a common finite subextension and use the same square.
Base change identifies the conditional restriction with the existing finiteness restriction
and applies the existing proper base-change theorem for each bundled coefficient case.

Updated the existing node's proof and dependencies to this route. The integral-model route
of the unit is preserved; its realized statement/step lists are empty. Local irreducibility
settings keep the existing derived functors abstract during elaboration;
the settings precede the rationalization declaration to avoid expanding its implementation.
`import all MorphismDefs` is needed to expose the base-change construction for the comparison
proof even though its public declarations are already available through `Proper`.

## Proved and sorry left

Closed the two original holes:

- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_properProjectionMap_boundedConstructible_rational`
- `AlgebraicGeometry.ProEtale.CondensedRing.isIso_properBaseChange_boundedConstructible_rational`

The item has zero remaining holes. No holes are added or split off. The four previously proved
theorems are retained. Imported theorem dependencies retain their existing proof status.

## No longer needed

The following former direct proof dependencies are unnecessary for this assembly. This is
pruning of this node's proof route, not withdrawal of their declarations or modules. Some
remain indirect dependencies of the existing theorems used, or statement dependencies.

- `lem-sfb-derived-exchange-exact-normalization` — `Sheaf.Paper.DerivedExchangeExactNormalization`.
- `lem-weil-pbc-proper-fp-permanence` — `(definition or Mathlib leaf)`.
- `det-lem-integral-models-operations` — `Sheaf.Paper.IntegralModelsOperations`.
- `lem-weil-pbc-coefficient-exchange-mates` — `Sheaf.CategoryTheory.Adjunction.CoefficientExchange`.
- `lem-weil-pbc-qbar-condensed-push-counit` — `Sheaf.Paper.CondensedQbarExchangeRightAdjunct`.
- `lem-sfb-ringed-derived-monoidal-comparisons` — `Sheaf.SixFunctors.RingedDerivedMonoidalComparisons`.
- `lem-pur-ringed-coefficient-projection-cocycle` — `Sheaf.Paper.RingedCoefficientProjectionCocycle`.
- `det-prop-scalar-six-pullback` — `Sheaf.SixFunctors.ScalarSixPullback`.
- `def-sfb-dc-upper-star` — `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
- `def-sfb-dc-upper-star-comp` — `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
- `def-sfb-dc-lower-star` — `Sheaf.AlgebraicGeometry.ProEtaleBoundedConstructibleLowerStar`.
- `def-sfb-dc-upper-lower-adjunction` — `(definition or Mathlib leaf)`.
- `lem-sfb-common-field-lattice-generators` — `Sheaf.SixFunctors.CommonFieldLatticeGenerators`.
- `lem-weil-pbc-ringed-projection-mate-exact` — `Sheaf.Paper.ProjectionMateExact`.
- `lem-sfb-ringed-projection-first-shift` — `Sheaf.Paper.RingedProjectionFirstShift`.
- `lem-sf-triangle-two-out-of-three` — `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`.
- `det-lem-integral-models-generators` — `Sheaf.SixFunctors.IntegralModelsGenerators`.
- `lem-pd-module-ringed-topos-derived-comparison` — `Sheaf.Paper.ModuleRingedToposDerivedComparison`.

Removed the following obsolete maintainer tool-use approvals from this node (all other
approvals keep their original order):

- `det-prop-scalar-six-pullback`.
- `det-lem-integral-models-generators`.
- `lem-weil-pbc-ringed-projection-mate-exact`.
- `lem-weil-pbc-proper-fp-permanence`.
- `det-lem-integral-models-operations`.
- `lem-weil-pbc-coefficient-exchange-mates`.
- `lem-weil-pbc-adjunction-shift-compatibility-unique`.
- `lem-sf-triangulated-right-adjoint`.
- `lem-weil-pbc-commshift-nattrans-comp-whisker`.
- `lem-sf-triangle-two-out-of-three`.
- `lem-pd-module-ringed-topos-derived-comparison`.
- `lem-pur-ringed-coefficient-projection-cocycle`.
- `lem-sfb-ringed-derived-monoidal-comparisons`.
- `lem-sfb-ringed-projection-first-shift`.
- `lem-weil-pbc-qbar-condensed-push-counit`.

The objectwise integral-model route replaces the common-field lattice-generator construction,
its cone/shift induction, and the separate generic exchange/cocycle normalization assembly.
The proper base-change API already proves invertibility of the specified standard map.
No source-library declaration is removed. No existing public import is removed. The exploratory private import of
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Localizing` was omitted;
projection naturality uses the canonical mate directly.

## Where the brief, the DAG or earlier work was wrong

No statement correction was needed. The planned generator induction was longer than necessary:
the existing localization and filtered coefficient-descent APIs provide models for the actual
two bounded constructible inputs. The standard and conditional restricted base-change maps
have the same construction; only proof-irrelevant preservation witnesses differ. The source
integral theorem uses `Scheme.Over` instances, requiring explicit instances from the standing
`Over` objects when applying it.

Making the existing bundled projection data locally irreducible after the generic
comparison helpers avoids repeated expansion of its category and endpoints. Direct
projections from the coefficient transport theorem avoid unpacking its unused conclusions. No interface or definition repair is
required, and no other module is changed.

## Second reading by F1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
