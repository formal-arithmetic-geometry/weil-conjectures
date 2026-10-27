## What changed

Proved `WeilConjectures.AdicFiniteRealization.adic_finite_realization_cocone`
from the existing raw stage comparisons, normalized realization functor,
localized Hom comparison and finite-cone integral models, followed by three
strictly smaller pending interface lemmas.

The proof of `realization_image` supplies both directions of the essential-image
criterion: finite cohomology filtrations and a finite truncation tower give an
integral model; conversely, `constructible` and the realization object equality
transport bounds and local finite freeness. The lower bound is replaced by its
minimum with the upper bound, including acyclic and empty-scheme cases.
`core_exists` combines the actual stage identities, inverse chi scalar family,
realizations, Hom bijectivity and this criterion. The main theorem proves
Noetherianity, finite dimension, quasi-separatedness and stalkwise invertibility
of ell directly, then assembles all Data fields.

Moved the original data declarations into the publicly reexported
`Sheaf.Paper.AdicFiniteRealizationData` so the independent proof steps can import
them without an import cycle. Repaired `ScalarData.integral`: it is now the
normalized commuting diagram through the common single derived tensor with the
actual integral transition comparison, instead of HEq between arrows on distinct
tensor presentations. See
`coord/changes/U3-adic-finite-integral-normalization.md` for the old/new signatures
and the complete consumer check. No existing Lean importer required adaptation.

The data module's initial timing run exceeded the file limit. Profiling traced
this to expanded integral-normalization terms in generated ScalarData recursors.
Packaging the identical proposition as irreducible integralNormalization and
marking scalarComparison, sectionDerived and closureComparison irreducible
reduced the timing run to about 29 seconds. Their formulas are unchanged.

## Proved and sorry left

Closed the item's one original hole:
`WeilConjectures.AdicFiniteRealization.adic_finite_realization_cocone`.
The item contains zero remaining holes.

Added three public whole-proof holes, each strictly a part of the original argument:

- `WeilConjectures.AdicFiniteRealization.adic_finite_scalar_coherence`
  (`lem-sf-adic-finite-scalar-coherence`): finite scalar comparisons and their coherence.
- `WeilConjectures.AdicFiniteRealization.adic_finite_constructibility_comparison`
  (`lem-sf-adic-finite-constructibility-comparison`): native coefficient cocone and
  the four constructibility criteria, with no scalar tower equations.
- `WeilConjectures.AdicFiniteRealization.adic_closure_scalar_coherence`
  (`lem-sf-adic-closure-scalar-coherence`): extension of supplied finite coherence
  along supplied coefficient legs, with no existence or constructibility assertion.

This is a decomposition: one hole closed and three split off, net minus two holes.
The private helpers are fully proved, and the data module has no holes. The existing
imported pending theorems remain their owners' work.

## No longer needed

Removed direct proof imports of the following modules from the item:
`Sheaf.Paper.CondensedERealization`,
`Sheaf.Paper.IntegralStratifiedPerfectCharacterization`,
`Sheaf.Algebra.Homology.OrdinaryDerivedChangeOfRings`.
The first is bypassed for the construction of Core by the existing
RationalModuleRealizationFunctor, ConstructibleRationalHomComparison and
RationalRealizationFiniteConeModels interfaces. The last two are supplied within
the existing raw stage/realization proof dependencies and need no direct application
in the item. Their mathematical work remains a dependency of those upstream proofs.

The local-triviality, immersion restriction, scalar associator, internal tensor
normalization and condensed coefficient calculus imports occur only in the
appropriate split-off modules. Public imports needed by the existing data signatures
stay public in their reexported owner. Removed obsolete direct tool approvals from the item node for
`lem-weil-pbc-integral-stratified-perfect-characterization`,
`lem-weil-pbc-continuous-coefficient-realizations`,
`lem-weil-pbc-condensed-e-realization`, and `lem-pur-derived-change-of-rings`.
The replacement raw stage, Hom and filtration interfaces carry the needed work.
No declaration, source-library module,
quarantined file, parent node or unit route is withdrawn. No whole module is claimed
pruned from the target closure.

## Where the brief, the DAG or earlier work was wrong

`ScalarData.integral` used HEq between maps with nonidentical source objects.
In particular, the equal-field PBC transition is literally identity but the other
transition tensors with the coefficient ring. Their multiplication unitor cannot
be replaced by equality of derived objects. The corrected diagram retains the
published integral comparison and both normalized tensor flattenings.

The plan's sentence 'apply condensedE_realization' did not directly supply the
RationalModuleRealization structure required by Core. Existing rational Hom,
filtration-model and finite-cone declarations give the exact interface without
choosing a replacement functor. The proof uses those declarations as intended,
including the ones whose own proofs are pending.

Read BS 6.6.11, 6.8.8 and 6.8.11--6.8.15, and HRS Theorem 7.7 and Lemma 7.9.
The finite free condition includes rank zero; no global denominator bound or
unrestricted continuous Omega-valued coefficient ring is introduced. The three
new pending statements include identity fields, repeated and ramified towers and
the empty scheme. Their source and complete argument are in each docstring/node.
No second reader was started, as instructed by the dispatcher brief.

## New nodes

`def-sf-adic-finite-realization-data` owns the existing data declarations moved
without renaming, with the corrected integral normalization.

`lem-sf-adic-finite-scalar-coherence` isolates original steps 5--6 over finite fields.
It takes Core as input and provides no closure coefficient or constructibility data.

`lem-sf-adic-finite-constructibility-comparison` isolates original step 3 and the
normalized section-ring legs. It proves no scalar tower equations.

`lem-sf-adic-closure-scalar-coherence` isolates the final further-extension argument
of original step 6. It takes the entire finite scalar coherence and coefficient
cocone as inputs.

All searches were run through msearch (LeanFinder, Loogle, grep and LeanSearch)
and the imported blueprint was searched for adic finite realization, scalar closure
cocone and section constructibility. No matching Mathlib theorem or blueprint node
was found. Existing node/declaration searches located the Hom and cone-model route.
The change record is `coord/changes/U3-adic-finite-integral-normalization.md`.

## Second reading by U3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
