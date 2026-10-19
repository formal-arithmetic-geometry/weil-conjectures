## What changed

Proved AlgebraicGeometry.Scheme.pbcQbarPullFamily_existsUnique in
lean/Sheaf/Paper/PbcQbarCompletedPullback.lean without changing its signature.
Existence specializes pbcDescentOperations to the Cartesian square whose vertical
maps are identities and whose horizontal maps are f. Identity direct images preserve
the integral category by pbcActualDerivedDirectIdIso and
pbcIntegralUniformComplete_isTriangulated. Uniqueness identifies stage functors,
then cancels the invertible scalar comparisons in PbcPullbackBetaSpec to identify
inverse beta components. Extensionality and proof irrelevance finish the equality.
The selected family is therefore determined up to equality, as required by the
existing choice-based definition. No data construction or public signature changes.
On resumption, retained this proof and checked it against the current repository
signatures. A fresh lcompile.py run compiled the complete delivered module
successfully (exit 0); both added proof imports again passed import_direction.py.

## Proved and sorry left

Closed 1 of the original 2 holes:
AlgebraicGeometry.Scheme.pbcQbarPullFamily_existsUnique.
Added 0 holes; split off 0 theorems. This is a proof from existing declared
obligations, not a sorry-free proof of the transitive dependency closure.

The only sorry left in the delivered module is
AlgebraicGeometry.Scheme.pbcQbarIntegralPull_mem
(node def-weil-pbc-completed-pullback). It still needs the uniform finite-reduction
constructibility and compatible etale-origin arguments in its existing docstring.
Its signature and whole-proof sorry are unchanged. The analogous existing lemmas
PerAdic.integralPull_mem (Sheaf.Paper.AdicHeartPullbackFibres) and pbcPurityPull_mem
(Sheaf.Paper.RationalPurityPresentation) cannot be imported: import_direction.py
rejects both because they already reach this module. The former additionally has
separated finite-type base-field hypotheses absent here.

The prior attempt's unregistered constructibility and existence split-offs are
retained only in scratchpad/preserved-at-resumption, outside the delivery. Its
uniqueness argument is now proved and incorporated into the main proof.

## No longer needed

Removed direct proof imports Sheaf.Paper.IntegralOperationsPreserveConstructible
(node lem-pur-integral-operations-preserve-constructible) and
Sheaf.Paper.IntegralOperationsScalarComparisons
(node lem-pur-integral-operations-scalar-extension).
Their distinct strict-tower interfaces do not supply the actual family theorem;
the already declared pbcDescentOperations supplies precisely its existence clauses.
The proof imports Sheaf.Paper.PbcUniformCompleteTriangulated and
Sheaf.Paper.PbcActualRingedExchange for identity-direct-image preservation.
No blueprint unit or unit step is bypassed. No new modules are needed.
A source-only comparison of this item’s import closure removes the following
35 modules. Other targets or parent modules may still import them;
project-wide reachability and progress remain the ledger’s responsibility.

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ConstantFieldTensorCohomology`
- `Sheaf.Algebra.Homology.KInjectiveProducts`
- `Sheaf.Algebra.Homology.PrincipalKoszulQuotientTowers`
- `Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`
- `Sheaf.AlgebraicGeometry.ProEtaleTorAmplitude`
- `Sheaf.CategoryTheory.ClosedAdjunctionComparison`
- `Sheaf.CategoryTheory.CompactSupportRoosCofinality`
- `Sheaf.CategoryTheory.StrictTowerArithmeticRestriction`
- `Sheaf.CategoryTheory.TensorParameterComposition`
- `Sheaf.CategoryTheory.Triangulated.DerivedLimitLevelwiseIsomorphism`
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`
- `Sheaf.Paper.CoefficientHomZeroClass`
- `Sheaf.Paper.CoefficientRingedSequenceSite`
- `Sheaf.Paper.DerivedCompleteKoszulReconstruction`
- `Sheaf.Paper.FiniteCoefficientFlatModel`
- `Sheaf.Paper.FiniteTensorConstructibleCohomology`
- `Sheaf.Paper.FiniteTorAmplitude`
- `Sheaf.Paper.FiniteTorAmplitudeSites`
- `Sheaf.Paper.IntegralOperationsPreserveConstructible`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.Paper.IntegralOperationsScalarExtension`
- `Sheaf.Paper.IntegralResidueTor`
- `Sheaf.Paper.ProEtaleConstantModulePullbackComposition`
- `Sheaf.Paper.ProEtaleConstantModulePullbackHomology`
- `Sheaf.Paper.ProEtaleFiniteLocalConstancyPullback`
- `Sheaf.Paper.ProEtaleResidueModuleTensorHomology`
- `Sheaf.Paper.ProEtaleResidueTorTest`
- `Sheaf.Paper.ProEtaleRestrictedTensorFiniteLocalConstancy`
- `Sheaf.Paper.ProEtaleSheafificationTensorComparison`
- `WeilConjectures.CategoryTheory.DerivedCategory.FlatModelOfClass`
- `WeilConjectures.CategoryTheory.Sites.ReductionFlatModel`
- `WeilConjectures.ConstructibleSheaf.Presentation`
- `WeilConjectures.SixFunctors.Etale.Derived.Finiteness.FlatModel`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.FlatModel`

## Where the brief, the DAG or earlier work was wrong

The preserved attempt had an unfinished uniqueness proof and no report or matching
nodes for its split-offs. The existing descent theorem makes a new existence
obligation unnecessary. Both component proofs and the assembled module were checked
with lcompile.py; delivery preflight performs the declaration and axiom probes.
Edge cases: the identity square is Cartesian for every f, including empty schemes,
without properness, surjectivity or invertibility in a base field. The normalization
argument includes equal coefficient fields and uses no cancellation of arbitrary
maps: every cancelled factor is an isomorphism or its functorial image.

The definition node has no proof steps; the existing Lean docstring already
prescribes restriction, rationalization and normalized family descent. This proof
implements that route using the existing descent proposition. No definition-node
proof graph change is delivered: attaching the family theorem's descent dependency
to the ambient completed-pullback definition would create the spurious cycle
completed-pullback -> descent-functors -> qbar-category -> common-stage-calculus ->
scalar-extension -> completed-pullback. The node currently bundles the ambient
construction with its later Qbar restriction in its Lean declarations. This metadata
breadth should be separated by the maintainer; the actual Lean imports are acyclic
and both new proof imports passed import_direction.py.

## Second reading by P7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
