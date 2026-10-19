## What changed

Proved `AlgebraicGeometry.ProEtale.integralConstructibleCompactness` with its original
statement and public imports. The assembly proves the exact Ind realization, vanishing on
Ind targets, closure of Dic, both canonical finite-window Hom comparisons, and compactness
of bounded constructible complexes in their localizing closure.

The three intermediate modules retained from the earlier attempt now have complete proofs:
`IntegralIndHeartRealization`, `IntegralIndLowerTail`, and
`IntegralWindowCoproductComparison`. There are no postponed proofs in the delivery.
Their new nodes record the actual arguments and dependencies.

The heart proof obtains finite presentation from integral Ext continuity, uses the integral
constant-model Serre theorem, and reuses the existing coefficient-independent private
categorical arguments through `import all`. It proves the canonical presentation needed
for ambient kernel/cokernel closure directly from finite presentation. Degree-one continuity
and the generic pushout argument give extension closure. The realization is the existing
constructed Ind functor, with its Yoneda isomorphism and filtered-colimit preservation.

The lower-tail proof transports exact countable products across the internal/sectionwise
module equivalence and applies the proved general `CompactOfBoundedExt` argument. A final
truncation triangle handles the endpoint degree exactly. The window proof constructs the
truncation/coproduct comparisons, applies continuity to finite partial sums of uniformly
bounded-below representatives, and identifies the actual direct-sum map by colimit
universality. No rational-coefficient specialization is applied to integral coefficients.

The main, lower-tail and window proofs use generic private assemblies to avoid repeatedly normalizing
the concrete module category. The truncation proofs cache their coproduct instances to avoid
repeating typeclass search. No compiler limit is raised, no existing definition changes, and no
consumer is adapted. The proof-command change record is
`coord/changes/E7-integral-compactness-private-proof-helpers.md`.

The resumed lower-tail compile passed in 10.5 seconds after abstracting its filtered-colimit
factorization and endpoint arguments into private categorical lemmas. The resumed delivery dry run also passed compilation and preflight.

## Proved and sorry left

Original item: one hole, closed in
`AlgebraicGeometry.ProEtale.integralConstructibleCompactness`
(node `det-prop-int-compactness-compact`).

The three new intermediate declarations are also proved:

- `AlgebraicGeometry.ProEtale.integralIndHeartRealization`
  (`lem-integral-ind-heart-realization`).
- `AlgebraicGeometry.ProEtale.integralIndLowerTail`
  (`lem-integral-ind-lower-tail`).
- `AlgebraicGeometry.ProEtale.integralWindowCoproductComparison`
  (`lem-integral-window-coproduct-comparison`).

Holes added: zero. Holes left in the item: zero. Holes across all four delivered modules:
zero. No definition has a hole; no axiom or private postponed proof is added. These proofs
use the project's existing dependency declarations; their transitive axiom audit is the
preflight's responsibility, so this report does not claim completion of every dependency.

Edge cases: the identity cover and the zero finitely presented model prove constructibility
of zero, including the empty scheme. Finite partial sums include the empty sum. The
lower-tail statement retains no lower-bound hypothesis, and its endpoint is recovered by
a separate single-layer truncation argument. The window comparison accepts arbitrary target
complexes because truncGE places every window in the same lower range. The main proof
handles zero summands when shrinking large existing coproducts to their nonzero support.

## No longer needed

Removed these private imports from the original item:

- `Sheaf.Paper.IntegralConstructibleExt`: its finite-base-field signature does not fit;
  the proved intermediates use `Sheaf.SixFunctors.IntegralExtHomContinuity` instead.
- `Sheaf.Paper.IntegralConstructibleHeart`: the integral constant-model Serre theorem
  supplies the heart input in the actual coefficient presentation.
- `Sheaf.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses`: the existing direct
  internal-module Grothendieck instance suffices.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic` and
  `Mathlib.Algebra.Homology.HomologicalComplexLimits`: supplied by statement dependencies.
- `Sheaf.CategoryTheory.InternalAbelianSheafModuleEquivalence`,
  `Sheaf.CategoryTheory.YonedaDerivedExtComparison`, and
  `WeilConjectures.CategoryTheory.PushoutShortExactSequence`: confined to the lower
  realization or tail arguments, where the existing generic APIs are used.
- `Sheaf.CategoryTheory.GrothendieckDerivedCoproductsColimit`: needed by the window proof;
  the main assembly uses the smaller existence and homology APIs.
- `Sheaf.AlgebraicGeometry.ProEtaleLeftComplete` and
  `Sheaf.AlgebraicGeometry.ProEtaleProductsDerived`: the general source-library
  `CompactOfBoundedExt` proof supplies the lower-tail argument from exact products.

The parent no longer takes these as separate proof inputs:
`def-weil-pbc-internal-abelian-sheaf-module-equivalence`,
`lem-weil-pbc-ring-sheaves-grothendieck`, `sk-lem-int-integral-heart`, `sk-lem-int-ext`,
`lem-weil-pbc-derived-single-fully-faithful`, `lem-sfb-ind-filtered-colimits`,
`def-weil-pbc-category-colimit`, `lem-sfb-ind-arrow-presentation`, `def-sp-abelian`,
`lem-weil-pbc-pushout-short-exact-sequence`, `lem-coef-yoneda-derived-ext-comparison`,
`lem-weil-pbc-short-five-lemma`, `def-weil-t-structure`,
`lem-sf-derived-homology-long-exact`, `def-kun-truncations`, `det-pe-left-complete-iso`,
and `det-pe-products-derived`. Facts needed inside the three proved lower results remain
recorded there. No claim is made that these leave the whole target import closure.

The obsolete top-level tool approvals for internal-module equivalence, ring-sheaf
Grothendieckness, pushout extensions, Yoneda Ext comparison, short five lemma, homology
long exact sequences, left completeness and derived products are withdrawn from the parent;
its lower nodes record the relevant arguments. No module is withdrawn. The unit's heart,
continuity, uniform bound, lower-tail and finite-window route is retained.

The heart module also removes exploratory direct imports of
`IntegralLfpConstantModelComparison`, `Mathlib.Algebra.Field.ULift`,
`ProEtaleModuleConstructiblePullback`, and
`Mathlib.Algebra.Homology.HomologicalComplexLimits`: no proof references need them directly.

## Where the brief, the DAG or earlier work was wrong

The retained report described three postponed intermediate results, but the retained Lean
already contained proof attempts for all three. Those attempts needed repair: an unavailable
private helper was replaced by its finite-presentation/cofinality proof, the coproduct cocone
was transported along the discrete diagram isomorphism, and the countable-products universe
was made explicit. Compiler-service requests sometimes returned no answer; those transport
failures were retried separately from Lean errors. On resumption the final window proof also
needed a generic categorical assembly and explicit coproduct-instance caching to fit the
standard single-file compilation limit.

`integralConstructibleExt` requires finite-base-field and finite-coefficient packages that
are absent from this item's unchanged signature. `integralExtHomContinuous` has the needed
general-base-field interface. The existing rational Ind-heart conclusions concern a different
coefficient ring, so the proof instead reuses their proved generic categorical helpers with
the actual integral heart. The same distinction applies to the generic lower-tail result.

## New nodes

`lem-integral-ind-heart-realization` / `Sheaf.Paper.IntegralIndHeartRealization` isolates
paragraph (1)'s exact fully faithful Ind realization and image closure. It is proved from
integral continuity, integral constant-model Serre closure, and the existing generic Ind APIs.

`lem-integral-ind-lower-tail` / `Sheaf.Paper.IntegralIndLowerTail` isolates paragraph (2)'s
unbounded lower-tail vanishing. It is proved by continuity, exact countable products, the
general bounded-Ext/left-completeness argument, and the endpoint truncation triangle.

`lem-integral-window-coproduct-comparison` /
`Sheaf.Paper.IntegralWindowCoproductComparison` isolates paragraph (3)'s coprojection-induced
finite-window comparison. It is proved by explicit preservation and colimit arguments.

All three inherit the parent's chapter and unit, cite the precise source paragraphs, and
retain the actual recorded searches. None carries a new hole. The change record is
`coord/changes/E7-integral-compactness-private-proof-helpers.md`.

Final validation on 2026-10-19: `deliver3.py --no-push` passed compilation and
preflight (dry-run commit `49bef70903`, review class CODEX). The retained consumer-check
log records successful single-file compiles of all three unchanged direct consumers.

## Second reading by E7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
