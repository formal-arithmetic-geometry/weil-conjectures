## What changed

Proved three existing theorem bodies in `lean/Sheaf/SixFunctors/CoefDualFormulaScalarTranspose.lean`:
`finiteEtaleDualizing_plus`, `ordinaryPush_eq`, and `supportScalar_isIso` in namespace
`WeilConjectures.CoefDualFormulaScalarTranspose`. Statements, public imports and definition
bodies remain unchanged. The pushforward proof identifies the two prescribed ring maps by
uniqueness, then substitutes that equality in their common module-pushforward construction.
The support-scalar proof applies the existing integral coefficient comparison after the
residue Tor criterion. Added its proof import `Sheaf.Paper.IntegralResidueTor`.

Updated the item's node proof and proof dependencies to record these implemented steps.
Its remaining original main-theorem plan is retained. No new public declaration, new hole,
consumer adaptation or change record is needed. A theorem-local unused-section-variable
linter setting preserves the existing signature of `ordinaryPush_eq`.

## Proved and sorry left

Closed 3 of the original 8 holes, with no holes added and no decomposition:

- `WeilConjectures.CoefDualFormulaScalarTranspose.finiteEtaleDualizing_plus`
- `WeilConjectures.CoefDualFormulaScalarTranspose.ordinaryPush_eq`
- `WeilConjectures.CoefDualFormulaScalarTranspose.supportScalar_isIso`

Five original named public theorem holes remain unchanged, all attached to
`lem-coef-dual-formula-scalar-transpose`, with their existing source and complete proof
docstrings retained:

- `WeilConjectures.CoefDualFormulaScalarTranspose.trace_existsUnique`
- `WeilConjectures.CoefDualFormulaScalarTranspose.pullCompletion_existsUnique`
- `WeilConjectures.CoefDualFormulaScalarTranspose.formula_existsUnique`
- `WeilConjectures.CoefDualFormulaScalarTranspose.beta_isIso`
- `WeilConjectures.CoefDualFormulaScalarTranspose.coef_dual_formula_scalar_transpose`

The compiled partial proof uses existing project theorem dependencies that may themselves
still depend on sorry. This is not a claim that the entire module or target closure is
axiom-free. Final compilation is performed by lcompile.py and delivery preflight.

## No longer needed

Removed these private imports, unused by this partial implementation; declarations needed
by statements and definitions remain available through the unchanged public imports:

- `Sheaf.Paper.FiniteStageVerdierBiduality`
- `Sheaf.Paper.PullbackTorAmplitude`
- `Sheaf.Paper.FiniteTensorConstructibleCohomology`
- `Sheaf.Paper.FiniteCoefficientFlatModel`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType`
- `WeilConjectures.SixFunctors.Etale.Derived.Adjunctions`
- `Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage`
- `Sheaf.NumberTheory.Padics.CoefficientExtensionFinite`
- `Sheaf.Paper.FiniteFieldFiber`
- `Sheaf.Paper.FiniteTorAmplitude`
- `Sheaf.Paper.IntrinsicFiniteTorsionConstructibility`
- `Sheaf.Paper.SfDerivedDirectImage`
- `Sheaf.AlgebraicGeometry.ProEtaleConstantDerivedDirectImage`
- `Sheaf.Paper.SfIntegralReductionTower`
- `Sheaf.Paper.DerivedScalarExtensionRestrictionAdjunction`
- `WeilConjectures.CategoryTheory.Triangulated.DerivedLimit`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.CanonicalOriginCompactSupportComposition`
- `Sheaf.CategoryTheory.AbsoluteTraceExchange`
- `Sheaf.Paper.SemilinearDerivedSections`
- `Sheaf.Paper.CoefDerivedSystemEvaluationCalculus`
- `WeilConjectures.SixFunctors.Etale.Derived.IntegralCoefficients`
- `Sheaf.SixFunctors.IntegralVerdier`
- `Sheaf.Paper.IntegralOperationsScalarComparisons`
- `Sheaf.CategoryTheory.RingedStrictTowerHomotopyLimitIndependentCoefficients`
- `Sheaf.Paper.FiniteFreeCompletedScalarComparison`
- `Sheaf.Algebra.Homology.RingedInternalHomSignedCalculus`
- `Sheaf.Algebra.Homology.RingedInternalHomExactRestriction`
- `Sheaf.Paper.CoefficientRingedTensorHomModel`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `Sheaf.Paper.CoefficientHomRepresentativeEvaluation`
- `WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed`
- `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`
- `WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory`
- `Sheaf.Algebra.Homology.RhomGlobalSectionsOfUniverses`
- `Sheaf.Paper.DualityPairing`
- `Sheaf.Algebra.Homology.DerivedInternalHomOfUniverses`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint`
- `Sheaf.AlgebraicGeometry.ProEtaleDerivedCategory`
- `WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.Closed`
- `WeilConjectures.Compactification.NagataCompactification`
- `WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`
- `WeilConjectures.SixFunctors.Etale.Derived.Dualizing`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`
- `Sheaf.Paper.FiniteFreeCoefficientExtension`

No module is withdrawn and no DAG node is claimed globally unnecessary: the five remaining
obligations retain their planned dependencies. In particular, the finite trace/exchange,
coherent-system and total-limit argument has not been bypassed. The new integral residue
Tor and compact-support comparison dependencies are tools for the support-scalar helper,
not a replacement of the unit's duality route. The unit's `realized` fields are empty.

## Where the brief, the DAG or earlier work was wrong

The bounded-below helper follows directly from the source-library exceptional D+ preservation
lemma; it needs no new preservation theory. The support comparison is already known to be
invertible on the uniform finite-Tor domain by `integralCoefficientComparison`; residue Tor
identifies that domain with the actual constructible domain here. Its repeated finite-basis
argument is unnecessary in this helper.

The original sandbox contained two unverified proof attempts; the pushforward attempt
needed an explicit presentation of the forgotten commutative ring map and the pro-etale
base-change continuity instance. These are now supplied. The beta theorem available in
`CoefIntegralFiniteExtension` existentially chooses normalized tensor presentations; it
cannot be directly specialized to arbitrary supplied presentations without a presentation
independence argument. That original hole remains unchanged.

Edge cases: D+ preservation applies also to the empty scheme. The pushforward equality is
an adjunction/limit uniqueness identity without nonemptiness assumptions. Residue Tor and
the canonical coefficient comparison apply to zero complexes and empty schemes; no field
extension degree or unramifiedness restriction was added.

## Second reading by G1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
