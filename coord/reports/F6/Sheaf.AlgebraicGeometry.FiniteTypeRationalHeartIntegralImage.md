## What changed

Proved `AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeRationalHeart_integralImage`
with the exact statement recorded by its existing node. The assigned source was absent
from `lean/` and `quarantine/`, with no entry in `coord/rework.tsv`; the sandbox restores
that module and its recorded declaration rather than withdrawing it. The existing node's
Lean attachment and statement are unchanged.

The proof applies `continuousConstructible_integral_single_model`, takes the integral
model's zeroth cohomology, and uses exact localization to recover an ordinary integral
sheaf N rationalizing to F. It verifies bounded constructibility of N[0] using the
single-functor homology isomorphism and vanishing in all other degrees. Finally it
composes `integralScalarPushHom_isIso` with the direct image of the rationalization
isomorphism. The unused-section-variable linter is disabled only for this declaration to retain
its assigned geometric hypotheses, some of which the shorter proof does not use.
No arbitrary existence witness is used in a data definition: all witnesses
are eliminated within this theorem proof.

The existing `ContinuousIntegralPushComparison` theorem handles the actual normed E
and closed-unit-ball inclusion directly. The node's proof, proof_deps and proof_origin
now record this route. No source-library declaration, target, existing definition or
unit route is changed. The unit's integral-to-rational coefficient argument is retained.

## Proved and sorry left

Closed the one assigned hole in
`AlgebraicGeometry.ProEtale.CondensedRing.finiteTypeRationalHeart_integralImage`
(node `lem-sfb-finite-type-rational-heart-integral-image`). The delivered module has zero
`sorry` tokens. Added zero holes and zero split-off statements. This is a proof from
existing declared results, not a decomposition. No other module is changed.

## No longer needed

The proof no longer directly needs the following planned dependencies:

- `lem-sfb-normed-coefficient-realization` / `Sheaf.Paper.NormedCoefficientRealization`:
  the existing continuous integral push comparison works with the given normed E itself.
- `lem-sfb-localized-direct-image-comparison` / `Sheaf.Paper.LocalizedDirectImageComparison`:
  its finite embedded coefficient presentation is unnecessary; the proof instead uses
  `lem-weil-pbc-continuous-integral-push-comparison` /
  `Sheaf.Paper.ContinuousIntegralPushComparison` on N[0].

These nodes were removed from this node's proof_deps, not withdrawn from the library.
They may remain needed by other consumers. No module is claimed globally pruned.
`ContinuousConstructibleIntegralSingle` and `ContinuousIntegralScalarExact` remain
needed. All non-public imports support the proof: the constructibility transport
lemma, the proved zero-module constructibility helper (through `import all`), scalar
comparison, and the Noetherian geometry API.

## Where the brief, the DAG or earlier work was wrong

The DAG and S1's landed report record this module and its one hole, but its source was
absent when this worker began; the parent `FiniteTypeDirectImageSingleBound` source
also still contained its original hole. There is no quarantine/rework row or current
F6 return for this item. The recorded exact signature was therefore used to restore
the assigned source in the sandbox; nothing was deleted or treated as obsolete.

The planned degree-zero model theorem supplies a derived integral model, not an
ordinary sheaf model in its signature. Exactness and zeroth cohomology bridge that gap;
this step is written explicitly in Lean. The existing continuous integral push
comparison removes the need to transport E to an embedded field.

Searches via msearch.py: LeanFinder returned eight generic sheaf/condensed-module hits;
Loogle on singleFunctor and leftDerivedFunctor returned no hits; Mathlib grep returned
no integral-comparison theorem. Direct project searches found the published integral
model and continuous push comparison used here. The relevant Bhatt--Scholze PDF text
(Lemmas 6.8.12–6.8.13, Proposition 6.8.14 and Remark 6.8.15) and the unit record were read.
The zero sheaf and empty source are covered by the same homology and zero-object
arguments; no nonemptiness or positive-rank hypothesis is introduced.

## Second reading by F6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
