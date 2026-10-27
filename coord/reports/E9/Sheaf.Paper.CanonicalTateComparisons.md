## What changed

Filled two proofs in `Sheaf.Paper.CanonicalTateComparisons`, preserving every existing
statement, public definition body and original public import. The integral product transfers the existing
normalized module-sheaf multiplication to the total tensor of degree-zero complexes.
The existing proved private orientation helpers construct the sole nonzero tensor
summand, lift the module isomorphism, and extract its normalization and uniqueness.
They are accessed through a private proof import, avoiding duplicate helper code.
This is the degree-zero specialization of the established orientation product argument.

The integral pullback proof compares the specified augmentation to the ambient
operation unit, identifies ordinary pullback with the source Tate line, and applies
the normalized Roos completeness criterion. Its argument works for arbitrary scheme
morphisms and includes exponent zero and empty schemes.

Factored the repeated completeness-to-Roos-unit proof into the proved private lemma
`roosUnit_isIso_of_complete`; the already proved `integralTensorUnit_isIso` now uses it
as well. Local priorities select the existing standard derived-category instances,
and local reducibility settings prevent expansion of completed comparison data.
These proof-context changes retain the same localization and comparison objects.

Added proof imports `Sheaf.Paper.PositiveRootTensorProduct`,
`Sheaf.Paper.IntegralPullbackAugmentationAmbient`, and
`Sheaf.Paper.OrientationIntegralCoefficientTwists` with `import all` for its proved
private tensor helpers, and `Mathlib.CategoryTheory.Limits.HasLimits` with `import all`
for the colimit-model conversion. Updated this item's node to describe these proofs
and their actual dependencies. Two direct importers receive the compilation fixes and subdivisions described below; their
statements and theorem proof bodies are unchanged. One equality proof in the
rational consumer now explicitly supplies its finite stage, preserving the same
comparison object. Its original line/source and common-stage constructions are
re-exported from `Sheaf.SecSmoothPurity.RationalPurityLineComparisons` and
`Sheaf.SecSmoothPurity.RationalPurityCommonComparisons` after the full consumer
still exceeded the limit following those local optimizations. The consumer node's
attachment and proof dependencies record this compilation split; its statement,
original proof steps and unit route are unchanged.

After these optimizations, the full file still exceeded the 60-second limit
(60.3 seconds in the last profiled run, 111 seconds in the final unprofiled run).
Relocated its existing declarations into supporting compilation modules:
`Sheaf.Paper.CanonicalTateComplexComparisons`,
`Sheaf.Paper.CanonicalTateCompletedComparisons`, and
`Sheaf.Paper.CanonicalTateScalarComparisons`, and
`Sheaf.Paper.CanonicalTateCommonComparisons`. The original module re-exports their
chain and retains the reduction-square constructions. All existing
names, signatures, and public definition bodies are preserved. The four constructor nodes
attach the relocated declarations; they add no mathematical theorem or hole.
The first delivery attempt pushed nothing: its repeated compile put the naturality
consumer at 62 seconds despite the earlier 41.1-second successful run. Subdivided
that consumer into `Sheaf.Paper.CanonicalTateNaturalityLaws`,
`Sheaf.Paper.CanonicalTateOrdinaryNaturality`, and
`Sheaf.Paper.CanonicalTateScalarNaturality`, publicly re-exported by its original
module. Its original signatures, public definitions, proved theorem bodies, core
hole and final theorem are retained. The naturality/core node attachments and
constructor dependencies follow this file split.

The second delivery attempt also pushed nothing: its repeated compile put the
combined common-stage/reduction item file at 63 seconds. The common-stage
constructors now occupy the fourth supporting module named above, with the
unchanged common-product hole; the final item module has no local holes. The
reduction module still initially exceeded the limit after this separation. Local
opacity for the actual ring-module pullback/adjunction and the existing Mathlib
self-smallness instance reduce its profiled compile to 34.4 seconds, preserving
all existing statements and public definition bodies.

The interface-preservation change record is
`coord/changes/E9-canonical-tate-module-decomposition.md`.

Validation: every delivered Lean file passed `lcompile.py` with the unchanged
per-file limit, including all four naturality subdivisions and all three rational-purity
consumer subdivisions. The final packet contains twelve Lean files. Static checks preserve all 49 original item signatures
(including its existing private helper), all 41 rational-consumer public signatures,
and all original public imports. No profiling options or debug commands remain.

## Proved and sorry left

Closed 2 of the original 6 holes, with no new holes:

- `WeilConjectures.CanonicalTate.integralProductComplex_existsUnique`.
- `WeilConjectures.CanonicalTate.integralPullUnit_isIso`.

The following 4 original named holes remain unchanged, with their original source and proof descriptions:

- `WeilConjectures.CanonicalTate.finitePullSheaf_existsUnique`, attached to
  `def-pur-canonical-tate-complex-comparisons`.
- `WeilConjectures.CanonicalTate.finiteProductComplex_existsUnique`, attached to
  `def-pur-canonical-tate-complex-comparisons`.
- `WeilConjectures.CanonicalTate.finiteScalarSheaf_existsUnique`, attached to
  `def-pur-canonical-tate-scalar-comparisons`.
- `WeilConjectures.CanonicalTate.commonProduct_existsUnique`, attached to
  `def-pur-canonical-tate-common-comparisons`, relocated unchanged.

This is a partial proof delivery, with no new split-off theorem statements. Four
existing holes move to support modules as part of the compilation split; they are
not newly introduced holes. The two closed proofs
still depend on the already declared lower module-sheaf comparison theorems; they
are proofs from those declarations, not claims that all their dependencies are closed.

The compatibility-only consumer edits retain their original holes unchanged:

- `WeilConjectures.CanonicalTate.geometricTateCore`
  (`lem-pur-canonical-tate-arrow-naturality-core`).
- `WeilConjectures.RationalPurityCoherence.commonSupportComposition_existsUnique`
  (`def-pur-rational-purity-common-comparisons`, relocated unchanged).
- `WeilConjectures.RationalPurityCoherence.rationalPurityTraceCoherence`
  (`prop-pur-rational-purity-trace-coherence`).

These are not holes added or closed by this item.

## No longer needed

None. No mathematical node or module is pruned. Original public imports remain.
Proof imports are placed in the support module whose proof uses them; the original
module retains `SfDerivedDirectImage` for its ordinary adjunction calculation and
`PrincipalKoszulStrictReplacement` for its existing instance settings.
The imports removed from the original file are relocated as follows:

- `SfDerivedCompleteLegacyComparison`, `RoosIntrinsicCompletenessEquivalence`, and
  `Mathlib.Data.Nat.Prime.Infinite` are proof imports of the completed module.
- `Sheaf.Algebra.Homology.FlatSingleDerivedNormalization` is a proof import of the
  complex module.
- `Sheaf.AlgebraicGeometry.ProEtaleConstantOpenSquareExchange` is a proof import of
  the scalar module.

The naturality consumer's `Sheaf.SecSmoothPurity.CochainCoefficientArrows` proof
import moves to its ordinary and scalar comparison modules. None of its original
public imports is removed.

The new positive-root, ambient augmentation and private helper imports are used
in the complex and completed modules. The rational-purity consumer's original
prime, flat-single, positive-root, residue-Tor and unrestricted-twist proof imports
move to its line-comparison module. Its original private CanonicalTateComparisons
import remains available for the local standard-derived instance settings. The product needs the
existing normalized positive-root sheaf multiplication; the pullback needs the
existing ordinary line comparison and ambient augmentation comparison. All existing
coefficient-stage interfaces and the unit route remain in place.

## Where the brief, the DAG or earlier work was wrong

The old pullback docstring suggested reconstructing the finite quotients directly.
The existing ambient augmentation comparison and Roos completeness criterion supply
a shorter already-declared route, just as in the orientation module. The original
DAG's final list of six remaining holes is updated to four. The rework row records
an earlier quarantined dependency, but the current item source is present and was
preserved, with its Lean attachment and dependencies.

The rational consumer's original node cites a trace/coherence blueprint file that
is absent from the current latest snapshot. Its existing statements and original
proof route are preserved; the two new compilation nodes cite the current Tate
comparison definition and the current transport proof (Steps 2 and 4), respectively.
No target or unit statement is changed by this source-metadata observation.

## New nodes

- `def-pur-canonical-tate-complex-comparisons`: the existing degree-zero line,
  generator, product and flatness declarations, including the two unchanged finite
  holes and the newly proved integral product.
- `def-pur-canonical-tate-completed-comparisons`: the completed tensor and pullback
  constructions and their proved unit lemmas. No holes in this module.
- `def-pur-canonical-tate-scalar-comparisons`: the existing finite realization and
  scalar comparisons, including the unchanged finite scalar hole.

- `def-pur-rational-purity-line-comparisons`: the rational consumer's existing
  root-line, flatness, finite-Tor, shifted-line and source-comparison constructors.
  No holes in this support module.
- `def-pur-rational-purity-common-comparisons`: its existing rational/common support
  and source composition constructions and clauses; the original common-support
  uniqueness hole is relocated unchanged.

- `def-pur-canonical-tate-naturality-laws`: the original categorical equation
  predicates and their four coefficient-stage instances. No holes.
- `def-pur-canonical-tate-ordinary-naturality`: the original ordinary pullback
  square proof, complex maps and strict/root-system predicates. No holes.
- `def-pur-canonical-tate-scalar-naturality`: the original scalar pullback square
  proof, reduction sheaf-line map and strict coefficient predicates. No holes.

- `def-pur-canonical-tate-common-comparisons`: the original common-stage pullback,
  stage evaluation, product and square constructors, including the unchanged
  common-product hole.

These nine new nodes are compilation subdivisions of the existing nodes, not new
mathematical reductions. The original unit route and target statements are intact.

## Forced adaptations

Both direct importers are unclaimed. Their original copies were compiled against
the split. They finished without type errors but were refused by the unchanged
60-second limit:

- `Sheaf.Paper.CanonicalTateArrowNaturality`: `NOT ACCEPTED: this compile took
  70 s > 60 s`; a profiled run took 66 seconds, including 13 seconds of typeclass
  search. Added two local attribute commands after `open FrobeniusCoefficientTwists`:
  prioritize the existing standard integral/finite derived-category instances and
  keep the specified pullback/product and ring-module adjunction data opaque during
  elaboration. This version compiled in 41.1 seconds, but the first delivery's
  repeated compile took 62 seconds. Its law definitions, ordinary-comparison
  helpers and scalar-comparison helpers are now separate modules, publicly
  re-exported by the original final-theorem module. All source bodies and the
  original core hole are preserved. The scalar proof accesses the proved private
  ordinary conjugation helper through a private import. The original final theorem
  retains its local essentially-small instance context. This consumer has no
  direct Lean importers, checked across both roots.
- `Sheaf.SecSmoothPurity.RationalPurityTraceCoherence`: original `NOT ACCEPTED:
  this compile took 81 s > 60 s` (81.2 seconds reported). Changed its existing
  priority-3000 integral instance command to priority 5000 and also prioritized
  the existing scalar-reduction target derived instance. A profiled run compiled
  in 52.4 seconds, but the final unprofiled run still took 79.9 seconds. A labeled
  profile isolated 8.78 seconds elaborating `commonPullInclusion`. Moved its existing
  local `commonStageDerivedPullback` opacity command before this definition, and
  explicitly unfolded the wrapper and supplied `⟨i, K⟩` in the defining equality
  proof. The endpoints and eqToIso constructor are unchanged; proof irrelevance
  preserves exactly the same comparison object. This consumer has no direct Lean
  importers, as checked across both library roots. Even with this repair the
  whole file still took 92.3 seconds. Split the existing line/source constructors
  and common-stage constructors into two supporting modules, publicly re-exported
  by the original consumer. Its original signatures, comparison data, main theorem
  and common-support hole are retained; the latter moves to the common module.
  All three subdivisions compile successfully with the unchanged per-file limit.

Local elaboration settings and the explicit stage argument in one equality proof
change in these consumers. Every existing signature, public import, theorem proof
body and nonlocal attribute is preserved. The changed equality proof determines
exactly the same public comparison object. The change record names each consumer and its holder.

## Second reading by E9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
