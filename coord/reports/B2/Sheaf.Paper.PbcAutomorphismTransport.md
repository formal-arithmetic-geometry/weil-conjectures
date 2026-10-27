## What changed

Partial proof delivery for `Sheaf.Paper.PbcAutomorphismTransport`. Preserve every public
signature, definition body, attribute and public import. Add private proof imports
`import all Sheaf.Paper.CompletedTowerPullback` and
`import all Sheaf.Paper.FiniteStagePairCategory` to reuse the existing normalized
constructions and their private proof interfaces. Add one proved private helper
`isoExactDerivedComparison` transporting the existing exact-derived counit comparison
along equality of ordinary functors.

The coefficient map is the hom of the existing canonical integral ring isomorphism.
The module-pullback equality follows from the existing tensor object/map equations.
The derived comparison follows from the normalized universal left-derived comparison.
The integral scalar comparison is the componentwise lift of its ambient comparison.
Rationalization commutes with transport on pure tensors. Finally compose the five
specified integral comparisons and descend through the existing raw localization;
the fully faithful precomposition API gives its component formula and proves
normalization and uniqueness.

The final remote single-file compile passed without errors or warnings in 42.2
seconds (`ec6463aee9419e36aa255b21`).

Remote checks use only the prescribed `lcompile.py` and delivery tool; no local
Lean or Lake command is run. All 27 original declaration signatures compare verbatim
against the shared source.

Update the existing node's proof metadata to record these arguments and explicitly
retain the original unfinished obligations. No new node or statement is introduced.

## Proved and sorry left

Six of the original thirteen holes closed, with no holes added or split off:

- `AlgebraicGeometry.Scheme.pbcIsoCoefficientMap_isIso`.
- `AlgebraicGeometry.Scheme.pbcIsoModulePullback_eq_completed`.
- `AlgebraicGeometry.Scheme.pbcIsoOrdinaryDerivedComparison_exists`.
- `AlgebraicGeometry.Scheme.pbcIsoIntegralScalarComparison_exists`.
- `AlgebraicGeometry.Scheme.pbcIsoRationalization`.
- `AlgebraicGeometry.Scheme.pbcIsoRationalScalarComparison_exists`.

Seven original holes retained verbatim, all attached to
`def-wf-automorphism-completed-transport`:

- `AlgebraicGeometry.Scheme.pbcIsoModulePullback_isEquivalence`.
- `AlgebraicGeometry.Scheme.pbcIsoCompletedComparison_isIso`.
- `AlgebraicGeometry.Scheme.pbcIsoAmbientPullback_preserves`.
- `AlgebraicGeometry.Scheme.pbcIsoIntegralPullback_isEquivalence`.
- `AlgebraicGeometry.Scheme.pbcIsoIntegralPullback_linear`.
- `AlgebraicGeometry.Scheme.pbcIsoScalarRightComparison_exists`.
- `AlgebraicGeometry.Scheme.pbcIsoAmbientScalarComparison_exists`.

The new proofs use the pre-existing named declarations, including remaining holes
where prescribed. In particular this does not claim that all six declarations are
independent of every earlier sorry. This is a partial proof delivery, not a decomposition.

## No longer needed

None: no public or proof import is removed, no node or module is withdrawn, and no
unit step is bypassed. The original node has no realized unit statement or proof step.
The coefficient invertibility proof can reuse the already recorded canonical ring
isomorphism directly rather than repeat a limit-preservation argument. No new site,
completion, tensor, or rational-localization theory is needed for these six proofs.

## Where the brief, the DAG or earlier work was wrong

The node originally had empty proof metadata, although each Lean theorem has its own
proof description. The delivery records the actual partial route and the remaining
obligations. The signatures are unchanged, including unused scheme-isomorphism and
base hypotheses; two declaration-local unused-section-variable linter settings keep
these signatures intact. No mathematical statement is weakened or disputed.

The source-library boundary is respected: no WeilConjectures module is modified.
The identity automorphism, equality E = F, zero ring, empty scheme and zero ideal do
not require special cases: the closed proofs use universal properties and functorial
identities without nonemptiness, cancellation of coefficient elements, or proper
field inclusions. No arbitrary witness of mere existence is used to define new data.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
