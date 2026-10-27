## What changed

Replaced the sole sorry in `WeilConjectures.prop_coef_integral_dualizing` by a complete,
compiling assembly proof. The theorem statement is unchanged. The proof takes the published
limit of the strict finite-dualizing tower, applies `normalizedDVRTower_effectivity`, converts
legacy completeness through `sfDerivedComplete_iff_legacy`, and combines the resulting
canonical reduction isomorphisms with the finite bounds to establish integral
constructibility and the uniform Tor interval. The two mapping conclusions are then supplied
by the separate mapping-limit step for this same object and presentation.

Added `Sheaf.SixFunctors.IntegralDualizingFiniteBounds`, proving
`WeilConjectures.integralDualizing_finite_bounds` from the existing unit, Verdier preservation,
intrinsic Tor comparison, isomorphism closure and bounded flat model. Its proof has no sorry.
The finite-level parameter n=0 denotes the positive residue exponent 1; the proof also handles
d=0 and the empty scheme. No nonempty-scheme or positive-dimension assumption was introduced.

Added `Sheaf.SixFunctors.IntegralDualizingRoosModel` and
`Sheaf.SixFunctors.IntegralDualizingMappingLimit` for the two unfinished strict subarguments.
Their conclusions are proper parts of the original argument: the first has no
constructibility, support, Tor bound or mapping adjunction conclusion; the second assumes
a prescribed constructible object and coherent Roos presentation and constructs no object,
tower, completeness or bounds. Each remaining hole has a source, proof in words, and node.

Moved the original twelve definitions/instances, byte-for-byte unchanged, to the Roos-model
module, publicly reexported by the original module. This avoids a cycle between the
subarguments and the assembly theorem. Existing public imports remain public. The consumer
check lists all 72 downstream modules in
`coord/changes/Z6-integral-dualizing-model-interface.md`; none needs adaptation. The
original theorem clauses, including both mapping conclusions and the prescribed
counit transitions, retain their original signatures and meaning.

Validation: `lcompile.py --all` compiled all four modules with no diagnostics (exit code 0).
All Lean lines are at most 100 characters. Delivery runs the independent compiler/axiom and
preflight checks. No global build, direct Lean invocation, or shared-tree write was used.

## Proved and sorry left

Original module: one hole before, zero after. Closed the direct hole in
`WeilConjectures.prop_coef_integral_dualizing` (node `prop-coef-integral-dualizing`).
This is a decomposition, not a fully sorry-free integral dualizing theorem: it adds two
strictly smaller holes below the original theorem.

Also proved `WeilConjectures.integralDualizing_finite_bounds`
(node `lem-coef-integral-dualizing-finite-bounds`), with no direct sorry.

Every remaining direct hole in the delivery:

- `WeilConjectures.integralDualizing_roos_model`
  (`lem-coef-integral-dualizing-roos-model`): strict normalized finite-dualizing tower and
  the Roos triangle for the prescribed total derived limit.
- `WeilConjectures.integralDualizing_mapping_limit`
  (`lem-coef-integral-dualizing-mapping-limit`): natural mapping-complex and degree-zero
  adjunction for a given constructible coherent finite-dualizing limit.

Holes closed: 1 original; holes added: 2. Direct-hole net is -1. The delivery is a real
reduction with the finite bounds proved, and does not claim completion of either remaining
subargument or a positive sorry-ledger net.

## No longer needed

The original assembly no longer directly imports these proof modules:

- `Sheaf.Paper.NormalizedDVRTower`
- `WeilConjectures.AlgebraicGeometry.BoundedConstructibleComplexes`
- `Sheaf.Paper.IntegralCompactSupportPrescribedReductions`
- `Sheaf.Paper.IntegralResidueTor`
- `Sheaf.AlgebraicGeometry.ProEtaleCohomologicalSupport`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `Sheaf.Paper.FiniteFieldFiber`
- `Sheaf.CategoryTheory.Sites.RGammaDerivedLimit`
- `Sheaf.CategoryTheory.PreDerivedAdjointFunctorsGeneral`
- `Sheaf.Paper.CoefTowerCoaugmentation`
- `Sheaf.Paper.PointSectionsDerivedReduction`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Paper.ConstantCoefficientObjectsConstructible`
- `Sheaf.NumberTheory.Padics.ExtensionIntegersDvr`
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`
- `Sheaf.CategoryTheory.SequentialTowerEvaluationFull`
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic`
- `Sheaf.Paper.PointFibreEquivalence`
- `Sheaf.Paper.WeilVerdierPreservationStrata`
- `Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.ConstantCoefficientScalarNormalization`
- `Sheaf.SixFunctors.CoefTowerEvaluationPairing`
- `Sheaf.SixFunctors.CoefTowerTraceRectification`
- `Sheaf.SixFunctors.FiniteDualitySiteComparison`
- `Sheaf.SixFunctors.CoefTowerNaturalCurrying`
- `Sheaf.SixFunctors.FiniteMappingAdjunction`

These dependencies have not all become globally unnecessary: the appropriate finite,
strictification and mapping-limit steps are recorded in the new nodes. In particular the
finite dualizing, finite mapping adjunction, finite counit transition, tower pairing,
trace, coaugmentation and natural-currying route remains needed below the new steps.
No existing module or DAG node is withdrawn, and no globally pruned module is claimed.
All original approved `tool_uses` remain: the tools are still used by the subarguments.
The original node's direct proof dependencies now name the three new strict subarguments,
normalized effectivity, completeness comparison and the integral constructibility definition.

## Where the brief, the DAG or earlier work was wrong

The current blueprint has moved this node to
`sec-smooth-purity/sk-lem-sp-tower` and gives both an exceptional-adjoint description and
its equivalent finite mapping-limit description. This delivery preserves the locked Lean
statement and uses the latter explicitly retained description. The declared unit record
has no realized statement or proof-step nodes to bypass; no unit or chapter record changes.
No false source statement or target correction is asserted.

The existing effectivity coherence lemma quantifies the level indices implicitly, whereas
`IntegralDualizingLimitPresentation` quantifies them explicitly; the assembly supplies
`fun m n h ↦ hcoherent h`. Both quantify every quotient transition.
The existing finite bounds were not a ready-made declaration: the proof required conversion
between the two etale constructibility predicates, the canonical comparison to intrinsic
coefficients, and transport through the flat representative's homology isomorphism.

The sandbox already contained unfinished work when this provider-interrupted dispatch was
resumed. Its original `.budget` and deadline were retained; the prior compile results were
checked before changing or delivering anything. No earlier delivery was repeated.

## New nodes

`lem-coef-integral-dualizing-roos-model` states the tower/triangle subargument. Its module
also owns the relocated unchanged definitions. It records finite comparison, roof
strictification and derived-limit evaluation transport, leaving constructibility and duality
for the other steps.

`lem-coef-integral-dualizing-finite-bounds` is proved in Lean. It records the precise
finite-coefficient Verdier/Tor/support argument, including isomorphism transport and the
bounded flat-model support calculation.

`lem-coef-integral-dualizing-mapping-limit` states the adjunction subargument for an
already supplied coherent limit. Its proof in words retains the finite mapping adjunctions,
coherent counits, fixed trace, evaluation pairing, coaugmentation, natural currying and
complete-DVR limit, rather than replacing the entire original theorem by a renamed copy.

Change record: `coord/changes/Z6-integral-dualizing-model-interface.md`.

## Second reading by Z6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
