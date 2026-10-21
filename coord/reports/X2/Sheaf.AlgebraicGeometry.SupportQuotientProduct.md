## What changed

Proved `AlgebraicGeometry.Scheme.supportQuotient_product` in
`lean/Sheaf/AlgebraicGeometry/SupportQuotientProduct.lean` by the existing normalized
supported-coefficient tensor factorization. Private lemmas identify the recorded cokernels
with closed direct images, construct the reverse product map, and prove it invertible by
closed/open restriction. The generator is epic, yielding uniqueness and the exact quantified
naturality predicate. Flatness and the native K-flat localization theorem establish the two
specified derived comparisons.

The eight public definitions, their data, all existing docstrings and both public imports
are unchanged. The public theorem keeps its published text and elaborated type. This is a
reviewer correction (re-applied a third time, review of aeb2bc9): the proof is the private
`supportQuotient_product_aux`, stated with explicit `IsIso` categories under the module-local
braiding priority, and the public statement is elaborated outside that namespace block. As
delivered, the annotated statement elaborated to a different type (hash 1399746229 against the
published 4191245391). Added proof imports provide the existing fixed-scalar
flatness, monoidal inverse image, and open/closed APIs. The derived proof first works with generic
coefficients and then specializes the same named comparison to ModuleCat. Proved private cache equalities and a private elaboration
helper reuse its actual tensor dictionaries; Lean kernel-checks the resulting proof term.
Local elaboration commands are
recorded in `coord/changes/X2-support-quotient-product-elaboration.md`.
Updated the existing node's proof, proof dependencies and proof origin, and removed obsolete
entries from its maintainer `tool_uses` list without adding or reordering approvals.

## Proved and sorry left

Closed the one original hole: `AlgebraicGeometry.Scheme.supportQuotient_product`
(node `lem-pur-support-quotient-product`). There are no holes in the delivered module,
no holes added elsewhere, and no new public statements. The proof uses the existing
uniquely normalized coefficient tensor and quotient-flat theorems as declared; any holes
in those pre-existing dependencies remain their own items. All new private helpers are proved.

Validation: the final proof, with the unchanged delivery axiom probe appended,
compiled through the required `lcompile.py` server compiler in 53.2 seconds;
`SHEAF-PROBED 10` reported no direct holes or extra axioms. The probe's own long-line
warning is outside the delivered source. This repair was compiled again through
`lcompile.py` on the current server environment: exit code 0, 41.8 seconds, no
errors or warnings. The initial busy-server request returned exit code 124; the
subsequent compile succeeded without changing the Lean proof. A textual comparison confirms that all eight existing public
definition bodies are unchanged. The delivered Lean source contains zero `sorry` tokens.

## No longer needed

Removed these proof imports:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatOnSite`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`
- `Sheaf.Algebra.Homology.KFlat`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ClosedImmersionProducts`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm`
- `WeilConjectures.ConstructibleSheaf.ConstantModuleLocallyConstant`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor`
- `Sheaf.Algebra.Homology.KFlatIndependentCoefficients`

The cokernel comparison and open/closed detection replace the separate stalkwise
multiplication construction and transport through the etale/pro-etale tensor coherence
lemmas. Native fixed-scalar flatness and K-flat localization APIs replace the independent
ringed-site tensor framework in this proof. Removed proof dependencies:

- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `prop-weil-pbc-geometric-stalks-exact`
- `lem-weil-pbc-closed-immersion-products`
- `def-weil-finite-type-morphism`
- `lem-weil-pbc-ringed-topos-flat-module-pullback`
- `def-pc-flat-sheaf-modules`
- `def-pc-kflat-complex`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `def-pur-sheaf-tensor-product`
- `lem-pod-etale-stalk-tensor-scalar`
- `lem-weil-pbc-constant-module-locally-constant`
- `lem-sf-comparison-pullback-exact`
- `lem-weil-pbc-comparison-pullback`
- `lem-pur-cochain-pullback-tensor-coherence`
- `lem-weil-pbc-site-derived-tensor-descent`
- `def-kun-derived-tensor`
- `def-weil-derived-tensor`
- `lem-weil-pbc-inverse-image-composition-module-linear`

No file or public declaration is withdrawn, including declarations of the adopted source
library. Dependencies still used by other modules remain in the project. The two historical
comparison annotations in `stmt_deps` are left unchanged under the restricted node-edit rule;
they are not used by this proof. The unit's recorded realized statements and steps are retained.

Deleted obsolete `tool_uses` entries for these same unused dependencies; the remaining
entries keep their original order:

- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-inverse-image-stalk-germ`
- `prop-weil-pbc-geometric-stalks-exact`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `lem-weil-pbc-ringed-topos-flat-module-pullback`
- `lem-pod-etale-stalk-tensor-scalar`
- `lem-sf-comparison-pullback-exact`
- `lem-weil-pbc-comparison-pullback`
- `lem-pur-cochain-pullback-tensor-coherence`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-weil-pbc-inverse-image-composition-module-linear`
- `lem-weil-pbc-constant-module-locally-constant`
- `lem-weil-pbc-closed-immersion-products`

The source import graph also confirms that these 38 modules leave this module's
transitive import closure; other users may still need them:

- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback`
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.ClosedImmersionProducts`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinearCore`
- `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`
- `Sheaf.CategoryTheory.AlgebraicInverseImage`
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`
- `Sheaf.CategoryTheory.CochainCoefficientUniverseTransport`
- `Sheaf.CategoryTheory.Sites.InverseImageLocalFamilies`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorComparisonOfUniverses`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullback`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitExistence`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackUnitUnique`
- `Sheaf.Paper.RingedTopoiInverseImagePairing`
- `Sheaf.Paper.RingedTopoiInverseImageTensorComparison`
- `Sheaf.Paper.RingedTopoiInverseImageTensorPairingIsIso`
- `Sheaf.Paper.RingedTopoiScalarTensorComparison`
- `Sheaf.Paper.RingedTopoiTensorComparisonConstruction`
- `Sheaf.Paper.RingedTopoiTensorComparisonData`
- `Sheaf.Paper.RingedTopoiTensorSections`
- `Sheaf.SecSmoothPurity.CochainCoefficientArrows`
- `Sheaf.SecSmoothPurity.CochainComparisonMonoidalEquations`
- `Sheaf.SecSmoothPurity.CochainCompositeAlgebraic`
- `Sheaf.SecSmoothPurity.CochainCompositeHom`
- `Sheaf.SecSmoothPurity.CochainModuleAdjunction`
- `Sheaf.SecSmoothPurity.CochainPullbackTensorCoherence`
- `Sheaf.SecSmoothPurity.CochainTensorCoherenceData`
- `Sheaf.SecSmoothPurity.ModuleTensorCoefficientEquations`
- `Sheaf.SecSmoothPurity.ModuleTensorCompositionEquation`
- `Sheaf.SecSmoothPurity.ModuleTensorExtensionEquation`
- `Sheaf.SecSmoothPurity.ModuleTensorGenerators`
- `Sheaf.SecSmoothPurity.ModuleTensorMonoidalEquations`

The current re-split additionally names `lem-pur-etale-quotient-tensor-stalk-criterion`
and `lem-pur-support-quotient-pair-pullback`. Neither is used by the retained proof:
the existing normalized supported-coefficient factorization and closed/open detection
supply the isomorphism, and epic generator cancellation proves the exact quantified
naturality predicate. These two nodes and their modules
`Sheaf.AlgebraicGeometry.EtaleQuotientTensorStalkCriterion` and
`Sheaf.AlgebraicGeometry.SupportQuotientPairPullback` are no longer needed by this
proof; their declarations and metadata are not changed or withdrawn.

## Where the brief, the DAG or earlier work was wrong

The earlier eight-step DAG route and current six-step re-split are longer than necessary
given the already stated
supported-coefficient tensor factorization. That existing theorem supplies the reverse
product arrow with exactly the needed normalization; its signature does not itself assert
invertibility, so this delivery proves invertibility by complementary restrictions.
No disputed statement or weakened hypothesis was needed. Inference had to align the inherited coefficient braiding and cochain
monoidal shortcut instances. The generic coefficient API prevents kernel reduction of concrete derived tensor
objects during the final specialization.
The generator and all restriction arguments also cover zero coefficients, empty/full
supports, empty schemes and nonreduced supports.

Repair of return C-daa39 (head daa39b5a0): rebased the node packet on the current
repository record and restored its maintainer-owned `lean_audit` field verbatim.
Only the permitted proof fields and deletion-only `tool_uses` pruning differ from
the current node. The previously approved argument is retained. At the two product-generator epicness
steps, explicit `epi_comp'` applications compose the already proved epimorphisms;
`IsIso.epi_of_iso` obtains the first two from their existing isomorphism proofs,
avoiding the expensive final instance search that exceeded the current file limit.
No mathematical statement, public definition or import changes in this repair.
A local irreducibility attribute keeps `constantSheaf` folded throughout the proof;
scoped semireducibility permits the two private constant-tensor invertibility lemmas
to unfold it. These attributes end at the module boundary.


Repair of return C-13dc6 (head 13dc6b755): rebuilt the node packet from the current
`sheaf-dag` record and overlaid only the retained `proof`, `proof_deps`, `proof_origin`
and unchanged `lean` attachment, together with deletion-only `tool_uses` pruning.
The current `blueprint`, `reviewed`, `split_report`, `lean_audit`, statement,
statement dependencies, and all other protected metadata are preserved exactly.
This repairs the three forbidden field changes identified by the failed landing;
the independently approved Lean proof is unchanged.

## Second reading by X2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.

Reviewer note (aeb2bc9): the Lean file of this head is byte-identical to 13dc6b7. The
reviewer correction above was lost when that head was returned for its node file, so it is
re-applied here. The node file of this head is correct as delivered.
