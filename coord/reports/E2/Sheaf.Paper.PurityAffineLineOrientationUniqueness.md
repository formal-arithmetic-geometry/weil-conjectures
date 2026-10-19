## What changed

Preserved the existing declarations and signatures in
`Sheaf.Paper.PurityAffineLineOrientationUniqueness`. The theorem body now constructs the
restriction data from `affineLine_orientation`, proves its normalization, and proves
injectivity by lifting H0 morphisms to etale sheaves and testing their geometric stalks.
The existing `gysin_structure` bijection closes the derived Hom equality. Three proved
private lemmas show that the terminal map, the support unit and the supported restriction
are independent of the choice of normalized pair transport.

Added `Sheaf.Paper.PurityAffineLineSupportStalk` for the source's canonical local
support-fibre/stalk comparison, separately from the global injectivity and uniqueness
argument. Its proof lifts the Gysin model along the fully faithful comparison functor,
uses an etale trivializing cover to prove its stalk has rank one, and proves that a
linear map between coefficient lines whose image contains one is invertible.
`Sheaf.Paper.PurityAffineLineSupportStalkMap` now proves that factorization from
local zero-germ vanishing. It bundles the evaluation and restriction as linear maps,
constructs a section with normalized image one, and proves that this section generates
the stalk using injectivity of a self-map of the finite coefficient ring. The remaining
source lemma is isolated in `Sheaf.Paper.PurityAffineLineSupportRestrictionZeroGerm`.
The parent and local DAG proofs and dependencies describe this route. All four modules
and the unchanged direct consumer `Sheaf.Paper.CohomologicalSmoothnessTheorem`
compiled cleanly together through lcompile.py --all; the consumer took 17.9 seconds
and was then removed from the sandbox because it needs no adaptation. After final
import pruning, all four packet modules compiled cleanly again: ZeroGerm 9.7 seconds,
StalkMap 35.8 seconds, SupportStalk 25.4 seconds and the item 29.7 seconds.
No existing definition,
theorem signature or target changed.

## Proved and sorry left

The original hole in
`WeilConjectures.PurityFiniteSetting.affineLine_orientation_uniqueness` is replaced by a
complete Lean proof from the existing declarations and the new local comparison theorem.
The transport-independence lemmas are proved.

Also proved:
`WeilConjectures.PurityFiniteSetting.affineLine_support_stalk` from the local factorization
map, `affineLine_orientation` and `gysin_structure`. Its private rank-one-stalk lemma
and elementary coefficient-line invertibility lemma contain no holes.

Also proved:
`WeilConjectures.PurityFiniteSetting.affineLine_support_stalk_map`. Its proved private
helpers establish transport independence, the rank-one stalk, linearity of Gysin
evaluation, and the finite-line factorization from a kernel inclusion. It neither
assumes a factorization nor chooses one in a definition.

One hole added and still left:
`WeilConjectures.PurityFiniteSetting.affineLine_support_restriction_zero_germ`, node
`lem-pur-affine-line-support-restriction-zero-germ`. It asserts only that a sheaf map
whose value on the geometric stalk unit is zero has zero supported restriction at that
point. It asserts no factorization, isomorphism, global injectivity or uniqueness.
Its source is local vanishing/excision in Milne 9.4, 9.5 and 9.7 and the explicit
stalkwise-evaluation assertion in blueprint Step 2.

This is a decomposition: one original hole closed syntactically, one local hole added,
zero net holes closed. There are zero sorrys in the item, zero in SupportStalk, zero in
SupportStalkMap, and one in SupportRestrictionZeroGerm. Both the factorization and
isomorphism steps are complete Lean arguments from their displayed dependencies.

## No longer needed

The proof uses the Gysin Hom-to-sections bijection directly and compares etale morphisms
into H, so it does not separately construct a global rank-one trivialization, reprove
concentration via truncation or run an image-of-the-difference argument. Localization,
relative Kummer and support-pullback compatibility remain transitive dependencies
through the orientation, Gysin or local-comparison declarations; they are not globally
pruned.

Removed the following 21 proof imports from the original module:
- `WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`
- `Sheaf.AlgebraicGeometry.FixedFiniteExceptionalAt`
- `Sheaf.Paper.PurityAffineLineDatum`
- `Sheaf.Paper.PurityGysinStructure`
- `Sheaf.Paper.ConcentratedComplexShift`
- `Sheaf.AlgebraicGeometry.RetractedSupportLocalizationComparison`
- `Sheaf.Paper.PurTwistSheafLocallyFree`
- `Sheaf.Paper.ProEtaleConstructibleOrigin`
- `Sheaf.Paper.SupportedCohomologyHom`
- `Sheaf.AlgebraicGeometry.SupportLongExact`
- `Sheaf.Paper.ComparisonPullbackExact`
- `Sheaf.AlgebraicGeometry.CompactSupportComparisonUnit`
- `Sheaf.AlgebraicGeometry.SupportComparisonPullbackCoherence`
- `Sheaf.AlgebraicGeometry.GeometricPointCanonicalGerm`
- `Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful`
- `Mathlib.Algebra.Homology.DerivedCategory.HomologySequence`
- `Mathlib.CategoryTheory.Sites.Point.Basic`
- `Mathlib.CategoryTheory.Sites.Point.Skyscraper`
- `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
- `Sheaf.Paper.ConstructibleExceptionalAdjunctionCoefficients`
- `Sheaf.Paper.PurityRelativeKummer`

Removed direct dependencies of the parent node (some remain transitive through the
orientation or the new local lemma):
- `def-pur-conventions`
- `def-weil-exceptional-inverse-image`
- `def-pur-affine-line-datum`
- `lem-pur-concentrated-complex-shift`
- `lem-pur-retracted-support-localization-comparison`
- `lem-pur-twist-sheaf-locally-free`
- `lem-sf-proetale-constructible-origin`
- `lem-sf-derived-homology-long-exact`
- `prop-pur-gm-relative-kummer`
- `lem-pur-supported-hom`
- `thm-pur-with-support-exactness`
- `lem-weil-pbc-comparison-pullback`
- `thm-pur-rank-one-local-calculation`
- `lem-weil-pbc-derived-single-fully-faithful`
- `lem-weil-pbc-geometric-point-pullback-stalk`
- `prop-weil-pbc-geometric-stalks-exact`

Removed obsolete parent tool approvals, preserving the order of those retained:
- `lem-pur-concentrated-complex-shift`
- `lem-weil-pbc-derived-single-fully-faithful`
- `lem-weil-pbc-geometric-point-pullback-stalk`
- `prop-weil-pbc-geometric-stalks-exact`
- `lem-exc-closed-support-triangle`
- `lem-pc-right-derived-functor-triangulated`
- `prop-pur-kinjective-resolutions-exist`
- `lem-weil-derived-direct-image-composition`
- `def-weil-exceptional-inverse-image`
- `prop-weil-pbc-comparison-direct-image`
- `lem-sf-derived-homology-long-exact`
- `lem-pur-supported-hom`
- `prop-weil-pbc-inverse-image-modules-exact`
- `lem-weil-pbc-comparison-pullback`
- `def-weil-size-convention`
- `lem-weil-pbc-affine-scheme-qcqs`
- `def-weil-finite-type-morphism`
- `def-weil-quasi-separated-morphism`
- `lemma-weil-pbc-finite-stalk-formula`
- `lemma-weil-pbc-finite-direct-image-exact`
- `lem-pur-twist-sheaf-locally-free`
- `lem-sf-proetale-constructible-origin`

Cleanup also removed a constant-stalk import added during this session;
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.ConstantSheaf` is already public
in the support-stalk statement module. The new support modules also dropped
redundant imports of `WeilConjectures.ConstructibleSheaf.StalkCardinality`,
`WeilConjectures.Mathlib.CategoryTheory.Sites.Point.Skyscraper`,
`Mathlib.LinearAlgebra.Span.Basic`, and `Mathlib.Data.Fintype.Card`: the public
orientation imports already export their required declarations.

The parent uses fullness on ordinary etale sheaves, the generic constant-sheaf stalk
isomorphism, and the existing module-valued morphism stalk test. It therefore does not
need derived-single full faithfulness, a separate geometric-point category equivalence,
or an image-and-exactness argument.

No globally unreachable module is claimed: the listed removals are direct imports and
parent proof edges only. The constant-sheaf stalk isomorphism and the etale morphism stalk
test are existing generic source-library tools.

## Where the brief, the DAG or earlier work was wrong

The final dry run initially rejected all three new nodes because their searches
contained LeanFinder, Loogle and grep but no LeanSearch: LeanFinder and Loogle count
as one required family. Ran and recorded an actual LeanSearch query for each node;
its returned signatures supply no direct match. That run also noted a nonblocking
timeout of the item axiom probe, which the merge repeats; the ordinary item compile
passes in 32.0 seconds. Nothing was pushed by the failed dry run.
The repaired dry run passed preflight as CODEX. A separate probe importing the
compiled sandbox item then completed in 5.3 seconds: the item's transitive axiom set
is exactly propext, Classical.choice, Quot.sound and sorryAx. The latter reflects the
named remaining local lemma and existing proof dependencies. The temporary probe
was removed before submission.

The retained report described an older packet: it claimed that support_stalk was the
remaining hole, but that theorem had since been proved using support_stalk_map. The
report now records the actual declarations. The required initial dry run was performed
before editing; no delivery or push had been started by this resumed attempt. A fresh
compile found a parser error caused by set_option placed between a docstring and its
theorem; moving the option above the docstring repaired it without a signature change.
The Gysin statement already supplies the full Hom-to-sections bijection and an etale
model of H0. The parent's planned truncation and scalar-trivialization arguments can
therefore be omitted. The source's assertion that its supported restriction is exactly
stalkwise evaluation needs the explicit normalized local comparison recorded in the new
nodes; none of the read declarations states that whole compatibility formula.

Searched the blueprint and existing nodes for support/stalk comparisons. The supported
Hom pullback node provides normalized transports and adjoint compatibility, but does not
state the Gysin-chart-to-stalk equation. The relative-support coordinate model concerns
ambient chart-support stalks and signed normal-space twists, rather than the stalk on Y
of the finite exceptional object. The source-library affine-line orientation uniqueness
assumes a normalized Kummer datum and uses a different supported-class representation;
it cannot be applied to the displayed finite root-line/kernel-derived map without this
comparison. The supported-Hom adjunction-transpose and closed-support-exceptional declarations were
also checked. The latter requires intrinsic constructibility of the raw support value,
which this local proof should not silently assume. The remaining lemma's proof in words
now uses the specified class adjunction at (id,s) directly. Representing both natural
support functors identifies their comparison with precomposition by an endomorphism;
this preserves zero pullback regardless of that endomorphism's value. Consequently the
stronger task of identifying the entire chart automorphism is unnecessary. Ordinary
finite closed direct-image exchange supplies the transpose argument; exceptional base
change is never assumed invertible. Neither closedSupportExceptionalComparison nor
supportedHom_adjunction_transpose is retained as a dependency of the new local lemma.
The coordinate-support
stalk API derives the ambient sheaf support kernel; identifying that object with the
specified exceptional value and its edge is the remaining comparison. The existing
regular-base-change theorem concerns a different coefficient ring and regular flat
base change, and does not supply that equation here. The finite-line construction removes the need to construct an exceptional base-change
map as part of the remaining lemma: it suffices to establish its zero-germ vanishing
consequence. This implication is a real linear-algebra proof: a normalized global
section forces evaluation to be onto the rank-one stalk, using finite coefficients.
Further Lean experiments in the sandbox proved the zero-germ-to-zero-etale-pullback
implication, the lifted Gysin morphism's zero derived pullback, uniqueness of normalized
edges from their cocycle formula, and the representable-functor and adjunction
naturality calculations preserving zero pullback. A further compiled calculation
combines the last two: every natural chart from Hom(A,R(-)) to a representable
functor preserves zero pullback when the ordinary direct-image exchange at A is
invertible; its proof evaluates naturality on the adjunction unit. The final
supported-Hom-to-zero-restriction implication also compiles for the actual pair
transport and coefficient pullback. A generic supported-pair helper avoids repeated
unfolding of the scheme-specialized support functor; the specialization compiles in
32.7 seconds. A further scratch proof constructs the additive global-section/Hom
equivalence explicitly from the two adjunctions, proves its naturality, and derives
that natural isomorphism on bounded-below categories. These are scratch proofs, not extra
landed statements or a claim that the remaining chart/Hom identification has compiled.
The new local proof uses `thm-sf-ambient-adjoint-class` to obtain the specified
exceptional Hom coordinates, `lem-sc-p1-rhom-hom-derived-roof` for the global
hypercohomology/Hom cocycle comparison, and `lemma-weil-pbc-finite-exchange` for
ordinary closed direct-image exchange. These supply the missing local comparison
calculation rather than replacing a blueprint unit. No false statement was identified. Empty Y has no points; disconnected Y is tested
point by point; the geometric field is not required to be finite type over k.

## New nodes

`lem-pur-affine-line-support-stalk`, in
`dag/nodes/sec-smooth-purity/lem-pur-affine-line-support-stalk.json`, records the local
canonical identification explicitly used in source proof Step 3 and the evaluation
compatibility of Step 2. It has a verbatim Lean statement, independent source and proof,
three logged search kinds, and the same chapter/unit as the parent. Its new module is
`Sheaf.Paper.PurityAffineLineSupportStalk`. No change record is necessary: no existing
statement or definition changed and no consumer adaptation was made.


`lem-pur-affine-line-support-stalk-map`, in
`dag/nodes/sec-smooth-purity/lem-pur-affine-line-support-stalk-map.json`, records the
separate local factorization from blueprint Step 2. Its module is
`Sheaf.Paper.PurityAffineLineSupportStalkMap`. Its proof now constructs that map by finite coefficient algebra from local zero-germ
vanishing, instead of leaving the entire factorization unproved. The support-stalk
node's proof and proof_deps follow its proved coefficient-line invertibility argument.

`lem-pur-affine-line-support-restriction-zero-germ`, in
`dag/nodes/sec-smooth-purity/lem-pur-affine-line-support-restriction-zero-germ.json`,
records the strictly local zero-germ vanishing consequence of source Step 2, with its
own Milne functoriality/excision source, complete natural-language proof, three logged
search kinds and verbatim Lean statement. Its module is
`Sheaf.Paper.PurityAffineLineSupportRestrictionZeroGerm`.

The dispatcher reference clock was reset on resumption: `.brief2` through `.brief5`
and `.budget.start` were recreated at 2026-10-19 17:07:48 UTC. The retained report is
from 2026-10-19 05:30 UTC, SupportStalk from 13:11 UTC, and SupportStalkMap from
14:35 UTC; the retained compiler logs extend through 15:53 UTC. The initial dry run
therefore reported zero elapsed minutes despite this earlier work. The budget and
launcher scripts were not edited. This records the metadata lifecycle problem for the
launcher owner; it is not a claim that waiting would prove the remaining comparison.

## Second reading by E2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
