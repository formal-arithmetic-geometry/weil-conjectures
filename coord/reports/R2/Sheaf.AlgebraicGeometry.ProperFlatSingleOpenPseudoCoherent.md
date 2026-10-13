## What changed

Replaced the sorry in `AlgebraicGeometry.properFlat_single_open_isPseudoCoherent` with a
complete Lean reduction. Its signature, universes, visibility and existing docstring remain
unchanged. Added five proof-only imports under `Sheaf.AlgebraicGeometry`:
`ProperFlatSingleOpenNoetherianComparison`, `NoetherianProperBoundedCoherentImage`,
`NoetherianBoundedCoherentPseudoCoherent`, `AffinePseudoCoherentLift`, and
`TensorPullbackStructureSheaf`.

Added two theorem modules. `ProperFlatSingleOpenNoetherianComparison` isolates approximation
and the termwise base-change comparison. It supplies a proper Noetherian source object with
bounded coherent cohomology and a comparison conditional on a finite-free representative of
its direct image. It supplies neither that representative nor pseudo-coherence of either
image. The additive functor is pinned by a natural isomorphism to tensor pullback followed by
inverse `overEquiv`. `NoetherianProperBoundedCoherentImage` isolates the proper Noetherian
image calculation, with no flatness, pseudo-coherence, finite-free or base-change assertion.

The item combines those parts, then applies the existing Noetherian pseudo-coherence
criterion and affine finite-free lifting theorem. It constructs the termwise image complex,
proves preservation of the upper bound and each finite rank, and applies the comparison.
Free preservation is proved using the tensor-pullback adjunction, its proved structure-sheaf
isomorphism and Mathlib's `SheafOfModules.mapFreeIso`; it is not hidden in either new hole.

Updated the item's node's proof, proof_deps and proof_origin, and added both new nodes. No
existing definition or statement changed and no other existing module was adapted. The old
rejected scratchpad files are outside the delivery set. No change record is needed.

## Proved and sorry left

Hole closed: `AlgebraicGeometry.properFlat_single_open_isPseudoCoherent`, node
`lem-pc-proper-flat-single-open-pseudo-coherent` (one of one item holes). There is no sorry
left in the item module.

Holes added:
- `AlgebraicGeometry.properFlat_single_open_noetherian_comparison`, node
  `lem-pc-proper-flat-single-open-noetherian-comparison`, in its own new module.
- `AlgebraicGeometry.Scheme.noetherian_proper_directImage_bounded_coherent`, node
  `lem-pc-noetherian-proper-bounded-coherent-image`, in its own new module.

Both are public theorems with exactly `:= by sorry`, a source and a complete proof in words.
This is a decomposition: one upper hole closed, two lower holes added, not a proof without
sorry dependencies or a claim of positive net hole progress. Neither new statement restates
the item. The model gives no target finite-free witness; its comparison requires a
representative of the stage image that it does not supply. The image calculation assumes a
Noetherian base and proves only bounded coherent cohomology. The existing criterion, affine
lift, and termwise construction are genuinely necessary and combined in the item.

The three delivered modules compile in import order with lcompile.py with no errors or
warnings after removing an overlapping instance binder and fixing docstring line lengths.
The deliver3.py --no-push dry run printed OK: compilation, axiom probes and the mechanical
preflight pass, except for the second reading which the independent reader must write.
Nothing was pushed. No axiom,
unsafe declaration, holed definition or arbitrary existence-based data definition was added.
All existential model data are eliminated only in a theorem proof.

## No longer needed

Existing imports removed: none. The final item does not import
`Sheaf.AlgebraicGeometry.DirectImageBoundedCoherent`: the attempted invocation was rejected
by the source import-cycle check, and was replaced by the strict proper-Noetherian
intermediate calculation. This is not a claim that its mathematics is unnecessary; the
Noetherian image step is retained.

Plan node `lem-pc-bounded-complex-tensor-proper-support-bound` and its module
`Sheaf.AlgebraicGeometry.BoundedComplexTensorProperSupportBound` are no longer needed on this
proof route. The descended morphism is made proper using eventual properness, so the
Noetherian image theorem applies directly without constructing a common union of supports
for the descended tensor's cohomology. Proper term supports for the approximation are still
needed and supplied using properness of the original morphism.

The approximation, perfect-tensor bounded coherence, relative base change, K-flatness,
open-base-change and independent-localization comparison steps remain needed through the
new model. The Noetherian criterion is invoked explicitly, and `AffinePseudoCoherentLift`
supplies the previously implicit finite-free representative. No stronger arbitrary-base
perfect-image or finite-affine-Cech perfect-image theorem is used or imported.

The second reading accounts for every old proof dependency. The following are retained
inside the comparison plan: `def-pc-perfect-complex`,
`def-pc-ringed-spaces-derived-direct-image`, `lem-pc-noetherian-approximation-data`,
`lem-pc-perfect-tensor-bounded-coherent`, `lem-pc-restrict-derived-direct-image-open`,
`lem-pc-rf-base-change-complex`, and `pqf-lem-coherent-ft-locnoeth`.
`lem-pc-bounded-above-flat-kflat` remains needed through
`lem-pc-flat-complex-derived-pullback`. `def-pur-pseudo-coherent-complex` and
`lem-pc-noetherian-bounded-coherent-pseudo-coherent` remain explicit in the item.
The two old nodes not used on this route are
`lem-pc-bounded-complex-tensor-proper-support-bound` and
`lem-pc-direct-image-bounded-coherent`; the latter module,
`Sheaf.AlgebraicGeometry.DirectImageBoundedCoherent`, is replaced on this route by
`NoetherianProperBoundedCoherentImage` because of the documented source import cycle.
This is route pruning, not a claim that either module is unreachable from all targets.

## Where the brief, the DAG or earlier work was wrong

The previous local-witness theorem was the unfolded original conclusion and not a reduction.
It has not been revived. The new source model gives no finite-free representative; the
Noetherian image calculation gives no target pseudo-coherence. The final item combines both
with existing criterion/lifting declarations and a real termwise preservation proof.

The original plan's `DirectImageBoundedCoherent` cannot currently be imported. deliver3.py
found this source import cycle, despite lcompile.py accepting the cached compiled modules:
`ProperFlatSingleOpenPseudoCoherent → DirectImageBoundedCoherent →
CoherentSupportProperHigherDirectImage → ModuleSupportProperOverBase →
ClosedImmersionPushforwardAnnihilated → AffinePushforwardBaseChange →
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.AffineMorphism →
WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.FiniteFreeComplex →
ProperFlatCechModel → ProperFlatCohomologyModel → ProperFlatCohomologyProperties →
ProperFlatFinitePresentationModel → ProperFlatBoundedPresentationModel →
ProperFlatAffineCechPerfectModel → FiniteAffineCechModelPerfect →
ProperFlatSingleDerivedDirectImagePerfect → ProperFlatSingleOpenPseudoCoherent`.
Names without a root in this path are under `Sheaf.AlgebraicGeometry`.
This is a dependency/interface problem in the existing plan, not a failure of the cycle
checker. It is reported here rather than bypassed. The new image theorem isolates exactly
the proper Noetherian calculation, removing the need to import that cyclic general module.
Its future proof should use proper coherence and the uniform cohomological bound directly;
it must not invoke arbitrary-base perfectness. No unrelated held module was edited.

The existing approximation interfaces also demand uniform same-universe derived localizations
on auxiliary schemes. The item supplies independent localizations only on X, S, U and U's
sites. The new comparison uses auxiliary localizations in universe u+1, where standard
localizations exist, then compares Q-images into the supplied target localizations. It does
not assume that arbitrary original-universe wS localizations exist on all schemes. This
universe/transport glue remains an explicit new proof obligation.

Edge cases checked mathematically: empty U has no x; zero F descends to zero tensor data;
empty Y and zero A have zero image; identity morphisms satisfy both intermediate assertions;
nonflat comparison maps are allowed because finite-free representatives are K-flat and
relative flatness is used for the descended tensor base-change comparison. Neither statement
claims a lower bound or finite Tor interval for the final representative. Compactness is
required only on auxiliary W, so the original U may be non-quasi-compact and nonaffine.

Read the official Stacks pages for 0A1H, 08E2, 08E8 and 08EE. The unit's Noetherian
approximation/proper-coherence/finite-free-model route is retained; the unit and chapter were
not changed. Blueprint searches for Noetherian approximation, bounded coherent, and 0A1H
found no duplicate of these typed intermediate statements. Mathlib searches through msearch.py
found no geometric model or bounded-coherent proper-image theorem. LeanSearch was unavailable
(Internal Server Error); LeanFinder, Loogle and source grep were also run. The existing affine
lift uses the correct Tag 08EE with an outdated lemma number (currently 36.13.3), requiring no
statement change.

## New nodes

`lem-pc-proper-flat-single-open-noetherian-comparison`, under
`dag/nodes/sec-picard-framework/`, supplies a proper Noetherian source and the comparison for
any subsequently supplied bounded-above finite-free representative. Its approximation step
now explicitly descends properness. Its stage source-coherence and comparison steps are
separate and name the existing nodes they use. It has no copied review metadata.

`lem-pc-noetherian-proper-bounded-coherent-image`, in the same directory, is the needed
proper-Noetherian specialization of the cyclic general proper-support image interface. It
asserts bounded coherent image cohomology without a model or base-change conclusion. Its
proof separates the coherent hypercohomology spectral sequence and the uniform upper bound.
Both nodes carry exact Lean signatures, sources, actual search records, blueprint ancestors,
chapter and unit. There are no change records or forced adaptations.

## Second reading by R2

Independent second reader, 2026-10-13. Reviewed the three delivered Lean modules, their
three nodes, the original item and node, the coherence unit, the cited sources, and the
sandbox report. Verdict: accept as a decomposition, with one item hole closed and two
strictly lower holes added; no positive net hole progress is claimed.

1. Interface preservation: `diff` shows only five plain proof imports and replacement
   of the existing theorem's proof. A byte comparison of the text from `theorem` through
   the start of `:=` confirms that its complete signature is identical. Universes,
   visibility, existing docstring and definitions are unchanged. The two other modules
   are new. The existing node changes only `proof`, `proof_deps` and `proof_origin`.
   No change record or forced adaptation is required.
2. Kernel/proof checks: independently compiled all three files in dependency order
   using lcompile.py, without errors or warnings. A scratch copy with explicit
   `#print axioms` for all three declarations reports exactly `propext`,
   `Classical.choice`, `Quot.sound`, and `sorryAx`. Source inspection finds only the
   two reported whole public theorem holes, no holed definition, forbidden declaration
   or extra proof hole. The item constructs K termwise; it eliminates existential data
   inside a theorem and introduces no arbitrary-witness data definition. Checked the
   directions of the unit/free isomorphisms and the unchanged upper bound.
3. New statements: the proper-Noetherian image lemma is precisely the proper case of
   [Stacks 08E2](https://stacks.math.columbia.edu/tag/08E2). Properness supplies finite
   type and proper closed supports, and the Noetherian base is quasi-compact for the
   uniform bound. The comparison lemma packages approximation and base change before
   any representative is chosen, following
   [Stacks 0A1H](https://stacks.math.columbia.edu/tag/0A1H) and eventual properness
   [Stacks 081F](https://stacks.math.columbia.edu/tag/081F). It does not assert the
   existence of P or the final pseudo-coherence. Both docstrings supply the construction
   and argument; neither hole is a renamed final conclusion. Checked empty U (no x),
   empty source, zero module/object, identity morphisms, rank zero and nonflat g:
   finite-free bounded-above P is K-flat, so nonflat g does not invalidate the comparison.
   Independent LeanFinder queries used the phrases "proper pushforward preserves
   coherent cohomology with finite cohomological amplitude" and "spreading out
   relatively flat sheaves and computing pullback of proper cohomology over finitely
   generated rings". Neither gave a replacement. Loogle free-sheaf search confirms the
   existing free-module API; source rg found the known general image lemma, whose
   cyclic import prevents its use here, and no acyclic duplicate of the new comparison.
4. Route and pruning: no shorter applicable proved geometric declaration was found.
   Each of the five new imports supplies an explicitly used theorem. Public imports
   of the new modules supply notions in their signatures; no proof-only public import
   was added. The Noetherian approximation, coherent proper image, finite-free lift
   and termwise base-change route retains the coherence unit's argument; its `realized`
   fields are untouched. Added an exhaustive accounting of the old proof dependencies
   to `## No longer needed`, explicitly naming the general image node/module replaced
   on this route. The K-flat dependency is retained through flatComplexDerivedPullback.
5. DAG agreement: checked each theorem against its node's Lean signature and statement;
   the existing item signature is unchanged. In all three nodes `proof_deps` is exactly
   the union of the steps' `uses`. The item steps match the actual proof: source model,
   bounded coherent image, Noetherian criterion, affine lift, and finite-free transport.
   New nodes carry sources, search records, creation metadata, blueprint ancestry,
   chapter/unit, and exact normalized Lean statements. Neither imports nor the nodes
   claim that the two lower statements have been proved.

Second reading changed only report.md: completed the pruning/dependency accounting and
added this independent review. No Lean or node repair was necessary. Neither new hole
can be closed by a few-minute application of an acyclic available theorem; both remain
explicit lower obligations. The scratch axiom-check copy was removed from the delivery.
