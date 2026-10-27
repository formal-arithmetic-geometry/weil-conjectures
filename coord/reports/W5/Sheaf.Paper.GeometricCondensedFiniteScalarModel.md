## What changed

Repair of the returned delivery `7e1612055e8` (reviewer `C-7e161`): the
mathematical review passed, but landing rejected a report fix addressed to the
basename `Sheaf.Paper.GeometricCondensedFiniteScalarModel.md`. The delivery's
report path is
`coord/reports/W5/Sheaf.Paper.GeometricCondensedFiniteScalarModel.md`, generated
from this sandbox's `report.md`. This resubmission retains the reviewed proof
changes, compares them against the current shared source, recompiles on the
project server, and uses the delivery tool to rebuild on current `sheaf-dag`.
The return requests no mathematical correction.
The server-only compile (`LCOMPILE_NO_LOCAL=1`) passed without diagnostics in
20.7 seconds. The current-source declaration comparison confirms that only the
four theorem bodies below changed: no signature, definition, or public import
changed, and the hole count is five before and one after.

Proved the four coefficient-construction theorems in
`Sheaf.Paper.GeometricCondensedFiniteScalarModel`, preserving every declaration
signature, definition, public import, and categorical normalization.

`finiteIntermediateFields_directed` uses Mathlib's finite-dimensional compositum
instance with the two lattice inclusions. `finiteValued_closed` uses the ground
field for zero and one, the compositum for sums and products, and the original
field for negation. `finiteValued_comp` retains the same image field.
`isSheaf_ringPresheaf` realizes the underlying presheaf as the universe lift of
a subfunctor of the continuous-map presheaf. The latter satisfies the profinite
coherent sheaf criterion. A covering sieve contains a finite effective-epimorphic
family; its joint surjectivity and the finite supremum of the image fields prove
that the descended function is finite-subextension-valued. This is the existing
proof of `Profinite.isSheaf_padicAlgClSubfunctor`, generalized to this item's
arbitrary coefficient universe and ambient normed field.

The coefficient proofs use neither algebraic closedness nor completeness, exactly
as their existing signatures require. Their constructions include the empty
profinite parameter and empty finite covering family: the supremum then is the
ground field and the pointwise condition is vacuous.

The final geometric comparison theorem is retained unchanged, with its original
named hole and proof plan. This packet is a partial proof of the module, closing
four existing holes without a decomposition or any added holes. The DAG route
for the remaining geometric theorem is unchanged; no node fields are changed.

## Proved and sorry left

Closed four of the original five holes:

- `AlgebraicGeometry.ProEtale.GeometricFiniteScalar.FiniteSubextension.finiteIntermediateFields_directed`.
- `AlgebraicGeometry.ProEtale.GeometricFiniteScalar.FiniteSubextension.finiteValued_closed`.
- `AlgebraicGeometry.ProEtale.GeometricFiniteScalar.FiniteSubextension.finiteValued_comp`.
- `AlgebraicGeometry.ProEtale.GeometricFiniteScalar.FiniteSubextension.isSheaf_ringPresheaf`.

One original hole remains:
`AlgebraicGeometry.ProEtale.GeometricFiniteScalar.geometric_condensed_finite_scalar_model`,
node `lem-sfb-geometric-condensed-finite-scalar-model`.
No holes added and none split off. The remaining theorem still requires the
normalized field-action assembly, finite representation cohomology, the two
scalar projections, and their square. No assertion here claims these are proved.

## No longer needed

Removed unused private proof imports:

- `WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible`.
- `Sheaf.AlgebraicGeometry.FiniteConstantLocalModel`.
- `Sheaf.Paper.AdicConstructibilityPredicateComparison`.
- `Sheaf.Paper.CoefficientHeartStratificationDefs`.
- `Sheaf.Paper.QlbarDirectImageComparison`.
- `Sheaf.AlgebraicGeometry.CondensedModulePullbackExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`.
- `Sheaf.SixFunctors.IntegralModelsGenerators`.
- `Sheaf.Paper.RingedProjectionFirstShift`.
- `WeilConjectures.Mathlib.CategoryTheory.Triangulated.Functor`.
- `Sheaf.Paper.RingedCoefficientProjectionCocycle`.

These imports are unused by the completed coefficient proofs. No dependency node
or module is claimed globally unnecessary: the final theorem is still open, and
its recorded geometric proof dependencies remain needed. No module withdrawn.
All public statement imports remain verbatim.

## Where the brief, the DAG or earlier work was wrong

No statement correction or disputed statement. The item node's main theorem is
not a direct application of its recorded input declarations. In particular:

- `QlbarDirectImageComparison` uses the canonical `PadicAlgCl` and its embedded
  finite field, whereas this item owns an arbitrary-Omega finite-valued ring.
  Applying it needs a coefficient and scalar-map transport, not unification.
- `FieldActionDerivedSectionTransport` supplies `CoefficientTransport`, whereas
  this item's `ScalarSystem.comparison` requires the richer descent `ScalarData`
  including invariant-side comparisons. Their compatible assembly still needs
  to be implemented.
- The finite cohomology model uses `normCoefficients`, `LisseTransport`, and
  module-topology continuous representations. This item's `CohomologyModel`
  additionally bundles a normed finite-dimensional carrier and joint action
  continuity. Their identification is part of the remaining geometric proof.

The continuous-map sheaf lemma in the adopted source is restricted to a Type-0
coefficient space. Its proof, using the universe-polymorphic Mathlib coherent
criterion, works here without changing the source library.

## Second reading by W5

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
