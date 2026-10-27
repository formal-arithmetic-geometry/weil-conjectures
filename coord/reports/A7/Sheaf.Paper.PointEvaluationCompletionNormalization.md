## What changed

Replaced the sole sorry of `Sheaf.Paper.PointEvaluationCompletionNormalization` by a
proof from two strictly smaller chain-level statements and existing library results.
All existing theorem signatures are unchanged. The existing public predicate
`betaCompletionEquation` now refers to the construction-owned
`PointSectionsCompletionEquation`, with exactly the same strict chain equation.
The item publicly imports its construction module. The change record is
`coord/changes/a7-point-completion-shared-equation.md`.
The proof establishes
K-flatness, invertibility of the actual completion units, their two coordinates,
quotient and chain naturality, the explicit completed pairing and its uniqueness,
and the localized inverse tensorator identity. The last identity follows by
naturality from the sections-completion chain square and the given canonical witness.

Added `Sheaf.Paper.PointBalancedQuotientTower` and
`Sheaf.Paper.PointSectionsBalancingCompletion`, each with one named public sorry,
a source, a full proof in words, and its own node. The first concerns only the
strict finite quotient towers. The second concerns only sections balancing and its
chain-level completion square for an arbitrary map eta. Neither restates the
original conjunction, assumes its conclusion, or supplies its derived pairing,
unit isomorphisms, uniqueness, or final localized identity.

Added proved private helpers for bounded-flat goodness, goodness of B[0] and the
total tensor, the actual unit's coordinates,
chain and quotient naturality, and invertibility of a constructible good complex's
localized identity-extension unit from `CompletedLineTensor.unit_normalization`
and `CompletedLineTensor.intrinsic_complete`. Private proof imports supply the bounded-flat
criterion, total-tensor criterion, and the normalized completed scalar unitor.
Quotient naturality is proved from the public scalar-reduction isomorphism and
the naturality of module sheafification on a pure tensor.

The proved private lemmas `isIso_map_iso`, `localized_pairing_square`, and
`sections_tensor_transport` perform the isomorphism, pairing cancellation, and final
tensor calculations over abstract categories. Its application uses the same recorded maps;
local folding keeps the large total and tower constructions out of repeated
rewrites. The combining proof stays in the item module. Synchronous elaboration avoids concurrent
checking of the large derived-category terms; all kernel and linter checks remain enabled.
The proof selects boundedness indices directly, avoiding large dependent elimination
motives. Proved private interfaces normalize the two imported balancing results at abstract
complexes. The combining proof chooses rho and beta from those interfaces.
The private lemma `beta_completion_chain` has the original raw chain square as
its conclusion and is proved directly by its hypothesis of type
`betaCompletionEquation`; this checks definitional equality of the shared predicate
with the old presentation. Mathlib's mapped-support instance preserves the strict
bound of the termwise realization directly. The generator rules determine rho and
beta; no data definition is chosen from an unproved existence assertion.

## Proved and sorry left

Closed the original hole in
`WeilConjectures.PointEvaluationCompletion.point_evaluation_completion_normalization`.
There are zero sorries left in the item module.

Added two holes:

- `WeilConjectures.point_balanced_quotient_tower`
  (`lem-pod-point-balanced-quotient-tower`).
- `WeilConjectures.point_sections_balancing_completion`
  (`lem-pod-point-sections-balancing-completion`).

This is a decomposition: one original hole closed, two strictly smaller holes
added; it is not a sorry-free proof and makes no claim of positive net hole progress.
The combining proof contains no sorry, axiom, or hollow definition.

## No longer needed

Removed these direct private proof imports:

- `Sheaf.Paper.IntegralDerivedOperationsOnSlices`.
- `Sheaf.Paper.IntegralPointCoefficientAdjunction`.
- `Sheaf.Paper.IntegralTensorReductionTowerComparison` (retained as a proof dependency
  of the new balanced quotient tower node, rather than discarded).
- `Sheaf.Paper.ConstantCompletionEquivalence`.
- `Sheaf.Paper.WeilCompletedTensorReflector`.
- `Sheaf.Paper.PointIntegralCompletedTensorComparisons`.
- `Sheaf.SixFunctors.PointRingedEvaluationModel` (retained as a proof dependency
  of the new sections balancing node).

The constructibility hypothesis on the ordinary total already makes chi an
isomorphism. Thus precomposition with chi gives uniqueness directly, and the
proof does not use the Noetherian coefficient adjunction, constant/Koszul completion
equivalence, or the completion reflector Hom-bijection. The supplied canonical
point tensor witness already gives the comparison equation; the separate completed
point tensor comparison theorem is unnecessary here. No module is withdrawn and
no claim is made that these modules are globally unreachable from all targets.

Removed obsolete top-level tool approvals for
`lem-weil-pbc-constant-completion-equivalence` and
`lem-weil-pbc-ringed-koszul-completion-reflector`; kept the remaining approvals in
order, including those used below the new tower lemma.

## Where the brief, the DAG or earlier work was wrong

The original proof plan's reflector argument is unnecessary under its own
complete-total hypothesis. Its tower comparison declaration gives only a natural
isomorphism, without the local generator normalization in its public result.
The point tensor canonical witness fixes its two completion coordinates, but the
public declarations do not yet state compatibility with sections balancing.
These two precise chain-level steps are the remaining holes. No existing statement
or definition was weakened, and the blueprint unit route is preserved.

The new nodes were checked for a dependency path back to the item; neither has one.
Blueprint searches for completion and balancing found no exact existing node.

The arbitrary-map and zero-complex cases were checked mathematically: neither
new lemma requires quasi-isomorphism of eta or finite Tor amplitude. The tower
formula is valid at n=0 (the first, exponent-one quotient), in all integer degrees,
and for zero scalars. The sections lemma uses no symmetry or degree permutation,
so introduces no extra Koszul sign.

## New nodes

`lem-pod-point-balanced-quotient-tower` is the original proof's steps 1--2:
strict balancing with its local formula. It lives in
`Sheaf.Paper.PointBalancedQuotientTower` and depends on the existing reduction
tower and identity scalar-extension APIs.

`lem-pod-point-sections-balancing-completion` is the chain-level part of the
original step 6: sections balancing and its two-coordinate completion square.
It lives in `Sheaf.Paper.PointSectionsBalancingCompletion`. Localization, transport
cancellation, and the inverse tensorator conclusion are proved in the item module.

The shared completion-equation definition and its public import are recorded in
`coord/changes/a7-point-completion-shared-equation.md`. The item node records the
new statement dependency. No downstream module imports the item, and its own
proof uses the unchanged raw chain equation through the proved private bridge.

## Second reading by A7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
