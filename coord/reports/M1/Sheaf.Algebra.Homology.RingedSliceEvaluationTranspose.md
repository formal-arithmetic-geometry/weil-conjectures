## What changed

`CategoryTheory.ringedSlice_evaluation_transpose` has a complete combining proof with its
original signature. It obtains normalized comparisons, proves the evaluation clause from
representative coherence, derives transposition by the actual adjunction counit bijection,
and applies the Koszul compatibility theorem. No target statement changes.

The twelve existing definitions are moved verbatim to
`Sheaf.Algebra.Homology.RingedSliceEvaluationModels` and publicly re-exported from the original
module, preserving every name, universe, body, visibility and transitive public import.
This breaks the otherwise unavoidable import cycle for the separate mathematical lemmas.
The existing definition node's Lean attachment follows the move.

`Sheaf.Algebra.Homology.RingedSliceKoszulCoherence` proves the symmetry clause. Its private
helpers prove pure-tensor generator extensionality using total-complex summands, the
sheafification adjunction and module tensor extensionality; transfer a symmetry square
along isomorphisms; and transfer commuting model squares through localization. The proof
then uses actual flat-term K-flat resolutions to cover arbitrary derived objects. It
cancels only isomorphisms, never evaluation.

Two separate source arguments remain as named holes: existence of normalized comparisons
and the evaluation-counit calculation on resolved representatives. The global evaluation
coherence theorem is proved: its private helpers derive evaluation naturality from the closed
structure and transport the square along isomorphisms; its main proof constructs K-flat and
K-injective resolutions and localizes their quasi-isomorphisms. Their docstrings and nodes
give full proof plans, including the fixed augmentation normalization and the additional K-flat resolution
of the Hom complex. Both are strictly parts of the original conjunction: neither asserts
transposition or symmetry compatibility, and the evaluation lemma does not construct data.

## Proved and sorry left

Closed the original hole in `CategoryTheory.ringedSlice_evaluation_transpose` (1 of 1).
Proved `CategoryTheory.ringedSlice_koszul_coherence` and
`CategoryTheory.ringedSlice_evaluation_coherence` with no holes; all private helpers are
proved. The adjunction-transpose argument is a complete Lean proof for arbitrary categories.

Added exactly two named holes:

- `CategoryTheory.ringedSlice_normalizedComparisons`, node
  `lem-weil-pbc-ringed-slice-normalized-comparisons`: existence of the normalized data only.
- `CategoryTheory.ringedSlice_representativeEvaluation`, node
  `lem-weil-pbc-ringed-slice-representative-evaluation`: the counit computation only on
  a flat-term K-flat source complex P and a K-injective target complex I, from the tensor
  and Hom model normalizations. The generalization to all derived objects is proved.

This is a decomposition, not an axiom-free proof of the whole result: one hole closed and
two added. The item module has zero holes; the complete delivery has two. There is no
`sorry` in any definition or private declaration. No arbitrary data is defined by choosing
an unproved existence witness.

Validation: all six modules are compiled in dependency order using `lcompile.py`. The
original theorem signature and the complete relocated definition block were compared as
text and are identical. Direct consumers DeltaRestriction, InternalSliceDerivedHomComparison
and RationalSliceCompletedEvaluation compiled unchanged against the re-export. The latter
two took 50.3 and 54.9 seconds. InternalSliceDerivedHomComparison also compiled against the
unchanged shared baseline in 53.1 seconds. RingedDerivedSliceData and the additional exact-use
consumer ModuleObjectRingedSiteDerivedComparison timed out at 60 seconds without compiler
errors. Both of these files also timed out unchanged against the shared baseline,
so these timeouts predate the delivery. No consumer was adapted.

Further proof work on the representative calculation constructed the additional K-flat
resolution of Hom(P,I), both uncurried chain maps, and the common-target square. The
remaining local calculation needs the Hom-component postcomposition formula and then
cancellation of the fixed augmentation squares. An attempted API proof repeatedly unfolded
the large chosen Hom bifunctor; it is not included as an unfinished private helper. A standalone equality of the two projection
specifications did compile after explicitly unfolding `homComplexFunctor`; the subsequent
componentwise postcomposition proof remains an unfinished experiment. The
retained theorem's docstring and DAG proof specify the common target explicitly, rather
than identifying two different fixed K-injective resolutions.

## No longer needed

The item itself no longer imports its former proof-dependency modules directly: the
construction argument and representative coherence are now their own nodes. This keeps the
original source route, including K-flat replacement, K-injective replacement, slice tensor
normalization, and derived descent. None of these mathematical dependencies is claimed
pruned from the target closure.

Removed these redundant direct private imports from the old module without adding them to
the construction node's imports:

- `Sheaf.CategoryTheory.RingedSiteKInjectiveResolutionsOfUniverses`: already available through
  the public fixed Hom representative interface.
- `Sheaf.Algebra.Homology.WeilSiteDerivedTensorDescent`: the independent-coefficient descent
  interface replaces this universe-specialized import in the construction plan.
- `Sheaf.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses`: total-tensor constructions
  are supplied by `CoefficientRingedTensorHomModel`.
- `Sheaf.Algebra.Homology.RingedInternalHomShiftOfUniverses`: shift comparison is not used in
  any evaluation, transpose or symmetry step.

Other original private imports for comparison construction are attached to
`RingedSliceNormalizedComparisons`; they are not claimed pruned. No upstream declaration,
module or public import is removed. No whole module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

No false statement was found. The original plan combines substantial comparison construction
and representative counit coherence with two formal consequences in a single hole. The
existing declarations of comparison existence do not pin all the representative squares
and the independent universes required here, so applying them alone would not prove the
statement. The new two lemmas isolate those precise source arguments instead of silently
choosing non-normalized comparisons. The unit route is retained; its realized statement
and step lists are empty, and no required unit is bypassed.

Edge checks: arbitrary unbounded representatives are retained; the Hom complex itself is
not assumed K-flat; the evaluation map is never inverted; zero objects and the zero ring
are admitted; the sign calculation retains odd degrees and uses units in Z; universe c,
v, u, w and w' stay independent. On a terminal slice the normalized maps are the usual
identity comparisons, consistent with all equations.

## New nodes

`lem-weil-pbc-ringed-slice-normalized-comparisons` records the source construction of the
normalized tensor and Hom comparisons and the two signed exchanges, independently of any
coherence conclusion. Its hole is in `RingedSliceNormalizedComparisons.lean`.

`lem-weil-pbc-ringed-slice-evaluation-coherence` records the proved categorical transport
argument and resolution construction reducing global evaluation to resolved representatives.
Its module has no holes.

`lem-weil-pbc-ringed-slice-representative-evaluation` records the remaining local counit
calculation on a K-flat resolution of Hom(P,I), comparison with the fixed K-injective
augmentations, and substitution into the model squares. Its hole is in
`RingedSliceRepresentativeEvaluation.lean`.

`lem-weil-pbc-ringed-slice-koszul-coherence` records the proved generator calculation and its
transport through localization and K-flat resolutions. Its module has no holes.

The change record is `coord/changes/M1-ringed-slice-model-module.md`. The existing theorem
node's proof dependencies now name the separate arguments and the unchanged model
interface; the definition node follows its verbatim implementation to the new module.

## Second reading by M1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
