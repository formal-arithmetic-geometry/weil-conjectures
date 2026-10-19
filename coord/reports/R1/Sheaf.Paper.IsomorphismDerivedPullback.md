## What changed

Completed all three remaining proofs in `Sheaf.Paper.IsomorphismDerivedPullback`.
The completed coefficient comparison follows from its limiting commutative-ring
cone and preservation by inverse image. The finite comparison uses scalar
extension along a ring isomorphism, uniqueness of left adjoints, exact derived
localization, and the existing constructible etale pullback theorem.

For integral coefficients, proved the bridge between the sectionwise and recorded
module inverse-image functors. Their adjoint coefficient maps agree after every
finite quotient projection; the constant case follows from sheafification
uniqueness. Uniqueness of module left adjoints and scalar transport then give the
ambient derived comparison. The existing completion-normalization theorem and
reconstruction-unit theorem supply the integral natural comparison. Transfer
constructibility across that comparison and evaluate at the regular coefficient
object. The auxiliary finite field is chosen with characteristic different from l.

Added only proved private helpers and proof imports. Every existing signature,
definition, instance and public import is preserved. The node's proof and
proof-dependency union now describe this argument. No new nodes or obligations.

## Proved and sorry left

Closed 3 of 3 original remaining holes, with 0 holes added and 0 left:

- `WeilConjectures.isomorphismCompletedCoefficientComparison_existsUnique`.
- `WeilConjectures.isomorphismFiniteDerivedPullback_termwise`.
- `WeilConjectures.isomorphismIntegralDerivedPullback_termwise`.

All three belong to node `lem-weil-isomorphism-derived-pullback`. The exactness
proof was already complete in the current source and is retained. Existing
imported results are used as stated, including the completion-normalization and
integral comparison-realization theorems; their separate proof obligations are
not duplicated here. No decomposition or split-off statement was introduced.

## No longer needed

Removed the following direct proof imports:

- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`.
- `Sheaf.Paper.IntegralReductionTowerWellDefined`.
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`.
- `Sheaf.AlgebraicGeometry.ProEtaleCountableProductsExact`.
- `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`.
- `Sheaf.Paper.CompletedIntegralConstantMapOfUniverses`.
- `Sheaf.Paper.DerivedCompleteOnSlices`.
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`.
- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`.
- `Sheaf.Paper.IntegralOperationsWellDefined`.
- `Sheaf.Paper.IntegralReductionTowerCanonical`.
- `Sheaf.Paper.IntegralReductionTowerWellDefinedUnrestricted`.
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`.
- `Sheaf.Paper.IsomorphismReductionTower`.
- `Sheaf.Paper.KFlatRingedToposPullback`.
- `Sheaf.Paper.PurInverseImageTensorHom`.
- `Sheaf.Paper.SfIntegralConstructible`.
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimitExistence`.

The completed finite proof needs no K-flat resolution. For the integral proof,
normalized completion and reconstruction are existing declarations, so this
module does not separately reprove tensor-complex, K-flat, reduction-tower,
countable-product or strict-Roos comparison lemmas. These can remain transitive
dependencies of the imported normalization theorems. No claim of global
unreachability is made, and no module is withdrawn.

The former direct planned dependencies removed from the node are:

- `lem-weil-pbc-exact-functor-complex-cohomology`.
- `lem-sf-exact-functor-derived-triangulated`.
- `lem-pc-kflat-resolution`.
- `def-weil-abstract-derived-category`.
- `lem-pur-isomorphism-inverse-image-tensor-hom`.
- `def-pc-tensor-complex-sheaves`.
- `lem-weil-pbc-ringed-topos-kflat-pullback`.
- `def-weil-pbc-proetale-site`.
- `def-weil-proetale-inverse-image`.
- `lem-weil-isomorphism-derived-pullback-reduction-tower`.
- `def-weil-integral-derived-reduction`.
- `def-weil-integral-reduction-tower`.
- `lem-weil-integral-reduction-tower-well-defined`.
- `lem-weil-proetale-countable-products-exact`.
- `lem-weil-derived-limit-existence`.
- `lem-weil-finite-free-completed-scalar-comparison`.
- `def-weil-derived-complete`.
- `def-pur-integral-derived-operations`.
- `lem-pur-integral-operations-well-defined`.

The old eight `tool_uses` approvals are withdrawn from this node because none is
used as a direct proof dependency by the implemented route. The report requests
reader assessment of the new completion-normalization and reconstruction tools;
the worker has added no tool approvals. The unit `sk-def-sf-admissible` has no
realized proof steps for this node to bypass.

## Where the brief, the DAG or earlier work was wrong

No false statement or definition was found. The old plan expanded completion and
its comparison at chain level, while existing normalized comparison declarations
already supply those parts. The retained earlier report described only the two
finite/completed-ring proofs and no longer matched its integral draft; this report
now describes all three completed proofs. Compiler repairs are confined to
private helper elaboration and proofs. No public interface or target changes.

## Second reading by R1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
