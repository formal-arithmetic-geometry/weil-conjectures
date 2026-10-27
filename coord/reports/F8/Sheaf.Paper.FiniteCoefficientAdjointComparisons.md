## What changed

Decomposed the simultaneous finite-coefficient adjoint system into three genuinely smaller
obligations: one stage/compactification adjunction, one coefficient-arrow comparison given its
endpoint data, and coherence given all individual data. The main theorem constructs retained
etale origins from Rnu and its comparison counit, chooses uniquely normalized data, assembles
FiniteTypeSystem, and proves all 24 displayed clauses by its fields and existing arithmetic.
The existing interfaces and proved arithmetic move verbatim to a public data module to avoid
an import cycle. This is an interface relocation, not a timeout split. No adopted source module
or target changes. The change record audits all downstream consumers.

## Proved and sorry left

One original hole is closed by decomposition, not by a complete mathematical proof:
`AlgebraicGeometry.FiniteCoefficientAdjoints.finite_coefficient_adjoint_comparisons`.
Three holes are added and remain, one named public theorem per new module:

- `AlgebraicGeometry.FiniteCoefficientAdjoints.finite_stage_normalized_adjunction`
  (`lem-pur-finite-stage-normalized-adjunction`)
- `AlgebraicGeometry.FiniteCoefficientAdjoints.finite_stage_normalized_change`
  (`lem-pur-finite-stage-normalized-change`)
- `AlgebraicGeometry.FiniteCoefficientAdjoints.finite_stage_normalized_coherence`
  (`lem-pur-finite-stage-normalized-coherence`)

The data module and assembly contain zero sorry. The existing arithmetic theorems remain proved;
this delivery does not count them as newly closed holes. The net hole change here is +2.
Each new existence theorem determines its data uniquely, so the assembly does not choose an
arbitrary object from an unproved mere-existence assertion. The private retainedOrigin helper
is a construction with proved fields, not a new hole.

## No longer needed

No mathematical node or module is withdrawn. The original direct dependency plan is partitioned
between the three new obligations; those dependencies still matter and are not claimed pruned.
The main assembly now imports just the data, the three new lemmas, and the proved etale-origin
API. Its old private proof imports not needed by the data are removed:

- `Sheaf.AlgebraicGeometry.Sites.FiniteTorsionEtaleCohomologicalDimension`
- `Sheaf.AlgebraicGeometry.Sites.TorsionEtaleCohomologicalDimension`
- `Sheaf.Paper.EtaleUnboundedRestrictionComparison`
- `Sheaf.AlgebraicGeometry.FiniteTypeDirectImageConstructibility`
- `Sheaf.AlgebraicGeometry.EtaleFlatConstructibleModel`
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`
- `Sheaf.AlgebraicGeometry.EtaleTorAmplitude`
- `WeilConjectures.AlgebraicGeometry.EtaleSheaves`
- `WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf`
- `WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `Sheaf.AlgebraicGeometry.FiniteConstantProjectionFormula`
- `Sheaf.AlgebraicGeometry.ResidueTorAmplitudeTest`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`
- `WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint` (both duplicate imports)
- `Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons`
- `Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality`
- `Sheaf.AlgebraicGeometry.CompactifiableOverField`
- `WeilConjectures.AlgebraicGeometry.DerivedCategories`
- `WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTorAmplitude`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `Sheaf.AlgebraicGeometry.EtaleFiniteTwistPullback`
- `Sheaf.Paper.RingedTopoiDerivedTensorPullback`
- `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.EtaleClosedImmersionEssentialImage`
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`
- `WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`
- `Sheaf.CategoryTheory.RingedSiteInjectiveMonoRestriction`
- `WeilConjectures.Algebra.Homology.KInjectiveRestrictLocalized`
- `WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp`
- `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`
- `Sheaf.CategoryTheory.KInjectiveTotalDerived`
- `Mathlib.Algebra.Homology.DerivedCategory.ShortExact`
- `Sheaf.AlgebraicGeometry.EtaleClosedSupportTriangle`
- `WeilConjectures.SixFunctors.OpenClosed.Stalk`
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtaleOver`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat`
- `Sheaf.Algebra.Homology.SheafRingDerivedCoefficientAdjunction`
- `Sheaf.Paper.EtaleProEtaleAdjunctionTransfer`
- `Sheaf.Paper.EtaleProEtaleCoefficientCompatibility`
- `Sheaf.SecSmoothPurity.ReductionExceptional`
- `Sheaf.SecSmoothPurity.ScalarExtensionFunctor`
- `Sheaf.Targets.VectorBundlePurity`

The seven original public imports are retained through the public data module. The arithmetic
nodes no longer depend on the system theorem: only their stage-definition dependency is needed.

## Where the brief, the DAG or earlier work was wrong

The plan's named geometric lemmas use several different category presentations: small ringed
coefficient models, universe-lifted coefficients, and the fixed ModuleCat derived categories of
this item's interfaces. They therefore do not directly supply its AdjointDatum/Change fields.
The new obligations isolate those geometric bridges, rather than assuming an unnormalized
adjunction or silently changing coefficient universes. Generic Mathlib adjunction and mate
results do not establish the missing geometric preservation or invertibility.

The arithmetic nodes' statement dependencies pointed at the whole system theorem although
only Stage/Arrow are needed. They now point to the existing coefficient-stage definition node.
This permits the actual proof dependencies to be recorded without an artificial cycle.
No false statement or target repair is asserted. Edge cases reviewed for the new obligations:
empty schemes, identity coefficient arrow, equal levels, nonflat quotient arrows, ramified
extensions, and arbitrary imperfect base fields. The hypotheses match the parent's argument;
no flatness of quotient scalar extension is introduced. Normalized adjunctions and changes are
unique because counits and projections fix their data, including on the zero category.

## New nodes

- `def-pur-finite-coefficient-adjoint-data`: relocated interfaces and arithmetic, no holes.
- `lem-pur-finite-stage-normalized-adjunction`: parent argument steps 1–4, one stage.
- `lem-pur-finite-stage-normalized-change`: parent steps 2–3 and 5–6, one arrow, endpoint data given.
- `lem-pur-finite-stage-normalized-coherence`: parent step 7, all individual data given.

Change record: `coord/changes/F8-finite-coefficient-adjoint-decomposition.md`.

## Second reading by F8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
