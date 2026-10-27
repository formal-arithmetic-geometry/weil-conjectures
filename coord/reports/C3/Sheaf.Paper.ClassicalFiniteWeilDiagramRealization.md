## What changed

Replaced the sole hole in
`WeilConjectures.classical_finite_weil_diagram_realization` with a complete Lean
assembly from three strictly smaller source steps. The original theorem signature
is unchanged. It now proves the finite sf expression equations from the descended
raw equations using an additive Hom map and preservation of signed list sums;
finite lissity from the supplied stage; finite clopen components from noetherianity,
local connectedness and compactness; and common-stage lissity by local free charts,
finite-stage pullback and transport through the stage and classical vertex isos.

Moved the 14 original definitions/declarations to
`Sheaf.Paper.ClassicalFiniteWeilDiagramData`, re-exported publicly by the original
module, to avoid cycles between the theorem and its proof-step modules. Signatures
and bodies match the originals verbatim; only the structure docstring gains its
new definition-node tag. There is no definition or target-statement change.

New statement modules isolate coherent normalized stages for an arbitrary supplied
R, simultaneous classical finite descent into supplied stages, and unique prescribed
Weil isomorphism lifting. Each has a source, full proof in words and a matching node.
No arbitrary object is defined by choosing a witness of an unproved existence theorem.
The assembly destructs existential conclusions only in a proof.

The data module, three split modules, and the main assembly each compiled through
lcompile.py. The last main-module compilation succeeded in 19.5 seconds with no
warnings. A subsequent attempted improvement of the lifting step could not compile:
server stdbuf could not create a temporary directory due to disk exhaustion. The
unverified experiment was removed, restoring the previously compiled split statement.
The final packet is submitted through deliver3.py for all required checks.

Change record: `coord/changes/C3-classical-finite-weil-diagram-data.md`.

## Proved and sorry left

Original holes: 1. Closed at the original declaration:
`WeilConjectures.classical_finite_weil_diagram_realization`.
The original module now has zero direct holes. This is a decomposition, not a
sorry-free proof of the mathematical theorem: 3 source-step holes are added, net -2.

Every remaining hole introduced by this delivery:

- `WeilConjectures.zl_coherent_normalized_diagram_stages`
  (lem-zl-coherent-normalized-diagram-stages), choosing a coherent family of pinned
  stages, independently of any finite diagram or prescribed isomorphism.
- `WeilConjectures.zl_finite_weil_diagram_descent`
  (lem-zl-finite-weil-diagram-descent), descending only classical objects, arrows,
  Weil data and raw equations to already supplied stages. It does not construct
  coefficient coherence, sf expression equations, or prescribed-object lifts.
- `WeilConjectures.zl_prescribed_weil_isomorphism_lifts`
  (lem-zl-prescribed-weil-isomorphism-lifts), the local Hom lifting and pinned
  common-stage transport step. It does not descend a diagram or choose stages.

Private proved helpers are `common_lisse_of_iso`, `common_lisse_of_finite`,
`map_signed_list`, and `finite_expression_value`. No private hole or definition
hole remains.

## No longer needed

Removed the following unused private proof imports from the original module:
Sheaf.Paper.GaloisLisseRepresentations;
Sheaf.Paper.LissePullbackNormalization;
Sheaf.Paper.RationalCoefficientCategoryComparison;
Sheaf.Paper.LisseCompletedCoefficientIso;
Sheaf.Paper.LisseCompletedPointwiseComparison;
Sheaf.Paper.LisseCompletedSystemComparison;
Sheaf.Paper.LisseCompletedTensorOperations;
Sheaf.RepresentationTheory.ProfiniteStableLattice;
Sheaf.SixFunctors.IntegralLisseReductionEquivalence.

Their mathematical ingredients remain in the proof plans of the appropriate split
steps where needed; this is not a claim that all of them leave the global closure.
All original public imports remain publicly available through the data re-export.

The direct proof does not use lem-zl-sf-pbc-normalized-heart-model or
lem-weil-pbc-noetherian-finitely-many-components: the inherited noetherian instance
and existing local connectedness/compactness facts prove the precise topology needed.
It also does not separately use lem-pod-separated-finite-type-base-change, whose
conclusion already underlies the inherited instance in NormalizedClassicalWeilRealization.
The direct pinning helpers lem-per-lisse-completed-coefficient-iso,
lem-per-lisse-completed-pointwise-comparison,
lem-per-lisse-completed-tensor-operations,
lem-fd-rational-coefficient-category-comparison and
lem-sfb-integral-lisse-reduction-equivalence are not separately needed by this
assembly: the split normalization step starts with R.pullback_pinning and uses
its recorded completed and lisse comparisons. Existing lower dependencies of those
interfaces remain intact. No source-library module or declaration is removed.

The parent's obsolete direct tool_uses entries are removed; lower source-step
plans still cite the necessary generic tools. No module is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The nine-step plan contains three substantial interface constructions rather than
immediate applications of its stated lemmas: normalizing all stages of an arbitrary
R to one Family; finite descent with free-system models and typed equations; and
transport of a prescribed finite module identification to the pinned common stage.
These are now explicit, independently actionable statements, strictly smaller than
the original conclusion. The parent proof node follows the actual compiled assembly.

No false statement or unit-route error was found. Zero rank, zero maps, empty diagrams,
empty Y and Frobenius permutations are still admitted without added hypotheses.

The server disk-full failure is infrastructure, not a Lean timeout; no launcher
script was changed or bypassed.

## New nodes

`def-zl-finite-weil-diagram-data` records the existing typed words, stages, equations,
coherence and prescribed-lift interface in its new data module. This is an interface
extraction with unchanged definitions, not a replacement notion.

`lem-zl-coherent-normalized-diagram-stages` isolates normalization/coherence for the
supplied R (parent steps 4--6 and 8), without a diagram.

`lem-zl-finite-weil-diagram-descent` isolates finite coefficient and free-system
descent (parent steps 2--3 and 7--8), into an already supplied stage family.

`lem-zl-prescribed-weil-isomorphism-lifts` isolates parent step 9, for every supplied
finite representative and common-stage arrow independently of the finite diagram.

Each new node has three kinds of recorded Mathlib searches. The blueprint/DAG
search found no exact duplicate. The unit route is unchanged.

## Second reading by C3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
