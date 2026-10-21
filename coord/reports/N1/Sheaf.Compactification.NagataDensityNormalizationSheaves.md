## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.nagataDensityNormalizationSheaves`
in the assigned module, preserving both public declarations and their exact types and
retaining every public import. Added proved private helpers `supportedUnit`,
`openUnit`, `cartesianCounit`, and `comparisonOfUnits`. The first lifts the existing abelian supported-unit
result through the actual scalar-extension adjunction; the other two lift the abelian
open unit and Cartesian essential-image argument through linearization and the scalar
equivalence. The last performs the unit/counit construction for abstract adjunctions,
avoiding reduction of the large sheaf-operation definitions during elaboration.
No definition, statement, or upstream module is changed.

The inverse of beta is constructed as the specified adjunction transpose, and its
invertibility follows from the open unit, pullback composition, and Cartesian counit.
Theta is exactly the closed unit followed by the pushforward of beta. The final two
clauses apply the complex functor and Q to this same natural isomorphism.

Added these proof imports: `WeilConjectures.SixFunctors.ProEtale.ModuleObject.OpenClosed`,
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.UnitCoherence`,
`WeilConjectures.CategoryTheory.ModuleObjects.ProjectionFormulaAdjunction`,
`WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.BaseChange`, and
`Sheaf.AlgebraicGeometry.ProEtaleAbelianClosedSupport`.

Updated the existing DAG node's proof, proof dependencies, and proof origin to match.
Removed its five obsolete tool approvals, without adding any approvals. The existing
abelian supported-unit and weakly-etale base-change nodes are used as generic tools;
they implement the same support and Cartesian-base-change steps inside this unit.
The geometric setup and the unit's extension-through-closure route are retained.

Validation: server compilation through lcompile.py and the delivery preflight.

## Proved and sorry left

Closed 1 of 1 existing holes:
`AlgebraicGeometry.ProEtale.CondensedRing.nagataDensityNormalizationSheaves`
(node `det-nagata-density-normalization-sheaves`). Added 0 holes. No sorry remains in
any delivered declaration. This is a proof, not a decomposition. Existing dependencies
may still use sorry; none is introduced or moved by this packet.

## No longer needed

Removed these private imports from the item:

- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`
- `Sheaf.CategoryTheory.RingedSiteModules`
- `Sheaf.CategoryTheory.SheafificationTensorLocalIso`
- `Sheaf.CategoryTheory.SheafTensorStructure`
- `Sheaf.AlgebraicGeometry.ProEtale.ClosedInverseImageLimits`
- `Sheaf.AlgebraicGeometry.ProEtaleOpenClosedSequenceRingSheaf`
- `Sheaf.AlgebraicGeometry.InternalModuleOperationsTransport`
- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.CategoryTheory.Localization.Predicate`

The explicit sectionwise transport and tensor reconstruction proof steps are unnecessary:
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`def-weil-sheaf-of-modules-category`, `det-def-sfb-sheaf-tensor-local-iso`,
`det-def-sfb-sheaf-tensor-structure`, `det-sf-open-closed-pullback-limits`,
`det-sf-open-closed-sequence-ring-sheaf`, and
`lem-sfb-internal-module-operations-transport` are no longer proof dependencies of this node.
The published scalar-extension, linearization, and forgetful APIs suffice instead.
`def-weil-finite-type-morphism`, `def-weil-open-immersion`, and
`lem-weil-pbc-noetherian-open-subscheme-noetherian` need not be separately cited: the
setup and existing geometric instances already supply the immersions and quasi-compactness.
`def-weil-pbc-proetale-site`, `def-sfb-module-upper-star`, and
`sk-def-sfb-pulled-back-coefficients` remain available through the statement imports,
but are not separate proof steps. `sk-def-sfb-coefficient-morphisms` remains used.

`lem-weil-pbc-exact-functor-derived-factorization` and
`lem-weil-pbc-localization-universal-property` are unnecessary for the exact clause
actually stated: Q maps the specified chain isomorphism to an isomorphism, so no
construction of descended functors is needed. No source declaration or module is
withdrawn. The retained public import ProEtaleModuleObjects still publicly imports SheafTensorStructure,
which privately uses SheafificationTensorLocalIso. Thus these two tensor modules remain in
the import closure; only their redundant direct imports and separate proof steps are removed.
Other consumers may still need all of these nodes and modules.

Removed obsolete `tool_uses` entries:
`det-sf-open-closed-sequence-ring-sheaf`,
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`lem-weil-pbc-exact-functor-derived-factorization`,
`lem-weil-pbc-localization-universal-property`, and
`det-def-sfb-sheaf-tensor-local-iso`.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan is sufficient in principle but substantially longer than the
published abelian support and module scalar/linearization APIs require. The pre-existing
theorem docstring describes that old plan and is preserved; the updated DAG records the
implemented proof. No false statement or definition repair was found. There was no
matching rework quarantine or current return for this module. The first compile request
returned exit code 124 because the server was busy; it was retried as instructed.

## Second reading by N1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
