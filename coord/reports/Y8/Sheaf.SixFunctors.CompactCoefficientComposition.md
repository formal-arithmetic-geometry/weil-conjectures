## What changed

Reduced AlgebraicGeometry.Etale.finiteCoefficient_compactSupport_composition to
the scalar-restriction compositor equation. The proved private tensor_compositor
calculation uses the universal Hom bijection, the four defining adjunct equations,
and naturality to prove the tensor equation. A proved restriction_map_hom API
lemma keeps the bounded-below wrapper folded in the calculation. The pro-etale
theorem retains its original hole and proof plan. Existing public signatures,
coefficient/compactification definitions and public imports are unchanged.
No source-library edits or consumer adaptations are needed.

## Proved and sorry left

This is a decomposition, with one original hole reduced and one smaller hole
added; no net hole reduction is claimed.

Original hole reduced:

- AlgebraicGeometry.Etale.finiteCoefficient_compactSupport_composition.

Original hole remaining:

- AlgebraicGeometry.ProEtale.finiteCoefficient_compactSupport_composition
  (lem-sf-compact-coefficient-composition).

New hole remaining:

- AlgebraicGeometry.Etale.compactSupportRestrictionPlus_compositor
  (lem-sf-etale-restriction-compositor), in
  Sheaf.SixFunctors.EtaleRestrictionCompositor.

The new statement has no tensor models or coefficient-extension comparisons.
The combination proof converts restriction coherence into tensor coherence using
universal-arrow injectivity, without faithfulness of derived scalar restriction.

## No longer needed

No module is withdrawn or claimed globally unreachable. The original node's
proof dependencies and tool approvals remain for the unproved pro-etale clause.
The following direct private imports are removed; required definitions remain
available through the retained public imports:

- Sheaf.AlgebraicGeometry.EtaleCompactSupportComparisons
- Sheaf.AlgebraicGeometry.Etale.DerivedExtensionZeroBaseChange
- Sheaf.AlgebraicGeometry.ExactUnboundedExchange
- WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
- Sheaf.AlgebraicGeometry.ProperOpenComparison
- Sheaf.AlgebraicGeometry.OpenSectionClopen
- Sheaf.AlgebraicGeometry.EtaleAmbientAdjointLocality
- Sheaf.AlgebraicGeometry.CompactifiableOverField
- WeilConjectures.AlgebraicGeometry.DerivedCategories
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
- WeilConjectures.SixFunctors.Etale.SmoothBaseChange.HigherDirectImage.FreeSheaf
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriekLeftAdjoint
- Sheaf.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
- Sheaf.Paper.UnboundedProperOpenInterchange
- Sheaf.AlgebraicGeometry.Etale.OpenImmersionLowerShriekCoherence
- Sheaf.AlgebraicGeometry.ProEtaleExtensionZeroComparison
- WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.CoherenceLegacy
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison
- WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
- WeilConjectures.SixFunctors.ProEtale.Comparison
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriek
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Iso
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Coherence
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
- WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
- WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FiniteType
- Sheaf.Algebra.Homology.DerivedChangeOfRingsIndependentCoefficients
- Sheaf.AlgebraicGeometry.ProperOpenComparisonSiteNormalization
- Sheaf.AlgebraicGeometry.ClopenSectionDirectImage
- Sheaf.AlgebraicGeometry.FixedComparisonDirectImageMate
- Sheaf.AlgebraicGeometry.CompatibleCompactificationTriangle
- Sheaf.Paper.ProjectionMateExact
- Sheaf.AlgebraicGeometry.ComparisonDirectImage
- Sheaf.AlgebraicGeometry.ProEtaleSiteComparison
- WeilConjectures.Compactification.NagataCompactification
- Sheaf.Algebra.Homology.DerivedChangeOfRingsCochainModel
- Sheaf.AlgebraicGeometry.CanonicalCompactSupportSiteComparison
- Sheaf.Paper.BoundedBelowCtfReflection
- Sheaf.Paper.ComparisonTorAmplitude
- Sheaf.Paper.ExchangeProjectionSuppliedDomains
- Sheaf.Paper.FiniteCoefficientDirectImage
- Sheaf.Paper.FiniteCoefficientFlatModel
- Sheaf.Paper.FiniteCoefficientReductionFlatModel
- Sheaf.Paper.FiniteTensorConstructibleCohomology
- Sheaf.Paper.OpenExtensionFiniteTor
- Sheaf.Paper.ProEtaleConstructibleOrigin
- Sheaf.Paper.ProEtaleFiniteCoefficientDirectImage
- Sheaf.Paper.ProperOpenCoefficientRefinement
- Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses

The etale calculation needs no new flat replacement or constructibility theorem
for its already quantified tensor models. Geometric triangle, proper/open mate
and refinement coherence remain within the new split node. The blueprint unit
sk-prop-sf-biduality-general has no realized nodes; its route is unchanged.

## Where the brief, the DAG or earlier work was wrong

The existing signature uses arbitrary universal tensor presentations, while the
previous scalar-extension composition lemma uses chosen tensor functors.
The universal-arrow calculation avoids extra normalization and transport lemmas.
No existing mathematical statement is disputed or changed.

Local reducibility attributes keep derived functors folded. A proved API lemma
exposes the bounded-below scalar restriction map instead of unfolding the large
wrapper throughout the proof. No definition body is changed.

The new restriction equation follows the construction of Stacks Tag 0F7J and
the first scalar-restriction square of Tag 0GL6; it is an explicit consequence,
not a verbatim source assertion. Its triangle comes from the supplied
compactifications, not an application of Nagata without qcqs hypotheses.
Identity ring/geometric maps, zero rings, empty schemes, zero input and nonflat
quotients were checked mathematically. No derived faithfulness is assumed.

## New nodes

lem-sf-etale-restriction-compositor records scalar restriction commuting with the
specified canonical compact-support compositor on the bounded-below small etale
site. Module: Sheaf.SixFunctors.EtaleRestrictionCompositor. Its docstring and node
contain the source-based proof plan. The main node appends the etale combination
route while retaining the original pro-etale route. No change record is required:
existing public statements, definition bodies and public imports are unchanged.

## Second reading by Y8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
