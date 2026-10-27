## What changed

Reduced `WeilConjectures.LisseLocalization.exists_lisseLocalizationRestriction` to three
strictly smaller steps. Its full original statement, binders and residue-field prime
instance are unchanged. The complete assembly constructs the existential witnesses,
obtains both tensor comparisons from the existing localized-site theorem, proves
concentration in degree zero from the two halves, identifies the single module with
the actual H^0, and proves the displayed Hom bijection by Mathlib full faithfulness
and isomorphism conjugation.

Moved the existing data declarations verbatim to the new definition owner
`Sheaf.Paper.LisseLocalizationData`, publicly re-exported by the item. This prevents
an import cycle between the substeps and the assembly theorem. The new owner retains
the original public prerequisites and has no proof holes. The change record is
`coord/changes/F6-lisse-localization-data-owner.md`.

## Proved and sorry left

Original holes: 1, in `exists_lisseLocalizationRestriction`.
That theorem now has a complete proof, as does the private helper `heart_image_single`.
The delivery is a decomposition, not a net proof: 1 upper hole closed and 3 smaller
holes added (net -2). The item itself has zero holes. The three remaining holes are:

- `WeilConjectures.LisseLocalization.nonempty_localizationData`, node
  `lem-tw-lisse-localization-existence`: single-scheme exact localization and raw descent.
- `WeilConjectures.LisseLocalization.localization_slice`, node
  `lem-tw-lisse-localization-slices`: one-chart coefficient/derived comparisons and
  normalized strict-limit realization, with the two localization models as inputs.
- `WeilConjectures.LisseLocalization.localization_localFreeness`, node
  `lem-tw-lisse-localization-local-freeness`: local freeness and the coefficient-unit
  image, with all localization and chart comparisons as inputs.

Each remaining theorem has its source, full proof in words, matching DAG node,
and an entire `by sorry` proof. No definition chooses arbitrary data from a mere
existence theorem: the final assembly only eliminates existential witnesses locally;
the moved data definitions are the original actual constructions.

## No longer needed

No mathematical dependency is withdrawn or declared globally unnecessary. The original
proof steps are retained by the smaller nodes. No source-library declaration is changed.
No module is withdrawn, and no unit statement or realized proof step is bypassed.

The item no longer imports directly the proof-only modules
`CompletedCoefficientRegularQuotients`, `CompletedCoefficientRingedCoherence`,
`RationalContinuousCoefficientDerivedLocalization`, `SliceRestrictionStrictDerivedLimit`,
`DerivedCompleteOnSlices`, `ExactFunctorDerivedFunctor`,
`ProEtaleWeaklyEtaleLocalization`, `FiniteTypeRestrictionExact`,
`RingedLocalizationRestriction`, `RingedTopoiCanonicalTensorPullbackOfUniverses`,
`ProEtaleObjectInverseImageRestriction`, and `DerivedLimitExistence`.
Their required assertions belong to the substeps, or are already public prerequisites
of the unchanged data types. `LocalizedSiteTensorRestriction` stays as a proof import
because the assembly actually applies it twice. `DerivedCategory.TStructure` stays for
the proved concentration argument. Original public imports remain re-exported by the
definition owner. Thus these import removals are organizational and redundancy pruning,
not claims that the mathematical substeps no longer require their tools.

## Where the brief, the DAG or earlier work was wrong

No mathematical statement error found. The generic localization lemma supplies a model
assertion with its own specified section action; constructing LocalizationData requires
reconciling that action with the independently recorded intrinsic constructible action.
Likewise the slice theorem supplies universal strict limits, while SliceLimitCompatibility
also requires normalized Roos realizations. Those interface assemblies are explicit
parts of the remaining substeps, not assumed definitional equalities.

The original file owned both the theorem and its data. Proper independently importable
substeps require separating the data owner, preserving every original declaration.
Profiling the extracted declarations reached modelTensorSection before timing out at
SliceLocalization. Disabling unused generated structure auxiliaries fixed this compile;
the data owner then compiled in 47.2 seconds at the unchanged time limit.

Edge cases checked in the new statements: arbitrary non-finite-type charts, empty scheme,
rank zero, varying ranks, separate rational-half integral representatives, unbounded
cohomology and torsion integral models. No global integral heart lattice is used.
The unit's recorded realized statement and steps are empty; the original node's route
through the localization, slice, strict-limit and completed-pullback arguments is retained.

## New nodes

`def-tw-lisse-localization-data`: definition owner for the original constructions,
LocalizationData, SliceCoefficients, SliceTensorCompatibility and SliceLocalization.
No existence claim and no new mathematical notion are introduced.

`lem-tw-lisse-localization-existence`: original proof steps 1-2 on a single scheme;
no slice, local-freeness, unit-image or Hom assertion.

`lem-tw-lisse-localization-slices`: original steps 3-5 for a single arbitrary chart,
with both models supplied. The tensor comparisons are proved in the parent, so the
new theorem does not repeat them as conclusions.

`lem-tw-lisse-localization-local-freeness`: original step 6 and the local-freeness/unit
part of step 7, conditional on the supplied localization and slice comparisons.
Concentration and the final Hom bijection are proved in the parent.

Sources read: Bhatt--Scholze 6.8.2, 6.8.3 and 6.8.14(2), and Stacks derived.tex
lemma-right-derived-exact-functor (015F), sites-cohomology.tex
lemma-derived-limit-is-ok (0941). All recorded proof-dependency Lean signatures were
read, and Mathlib concentration, full faithfulness and Hom conjugation were checked.
Searches used LeanSearch, LeanFinder, Loogle, msearch grep and local project/Mathlib rg.
Blueprint searches found no exact existing statement for these interface substeps.
The delivered dependency graph has no missing ids or new cycles.
The combined sandbox compile passed for all five modules, including the complete
assembly theorem and its private concentration helper. The exploratory partial proof
in the existence substep was then removed, leaving the required entire `by sorry`.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
