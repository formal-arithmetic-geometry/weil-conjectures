## What changed

Restored the assigned module from its quarantine archive and preserved the original
`component_composition_coherence` statement. Replaced its proof hole by two substantive
transport arguments. The projection argument transports a square on compatible
compactifications to arbitrary first and composite compactifications using input
naturality, compactification compatibility and `composition_comparison`. The associativity
argument applies binary support normalization four times, reflects canonical origin
associativity through the faithful realization, takes inverses and handles precisely the
compactification cast occurring in the original HEq.

Added explicit origin inclusion and support-comparison constructions. Their data are built
from the existing coefficient equivalence, supplied support realization and canonical
candidate comparisons. The existence of an etale-origin presentation is used only in
proofs. Added a proved input-naturality module by reusing the parent's existing private
argument without importing that parent (which would create a cycle). Added a proved
etale-origin property module. Updated the item's proof plan to match the Lean reduction.
No existing declaration signature, definition, instance, exported attribute or public import
changed. The compactification proof treats tensor and pullback locally as abstract functors
and cancels their identity maps with a proved generic lemma, avoiding expensive unfolding.

All five modules compile cleanly with `lcompile.py`; the final item check completed in
15.9 seconds. `deliver3.py` runs the required compilation, axiom and source checks.
Profiling options used during development have been removed.

## Proved and sorry left

Closed the one direct hole of
`WeilConjectures.CompactSupportFiniteProjection.component_composition_coherence`
(node `lem-sf-finite-projection-composition-transport`) by decomposition.

Proved the auxiliary declarations
`WeilConjectures.CompactSupportFiniteProjection.component_input_naturality`
(node `lem-sf-finite-projection-input-naturality`) and
`WeilConjectures.CompactSupportFiniteProjection.finiteRealization_etaleOrigin`
(node `lem-sf-finite-realization-etale-origin`), as well as the private categorical
cancellation and associativity-reflection lemmas in the item.

Two new direct holes remain:

- `WeilConjectures.CompactSupportFiniteProjection.exists_component_binary_square`
  (`lem-sf-finite-projection-binary-square`): the projection square for one compatible
  choice of first and composite compactifications, with the second prescribed.
- `WeilConjectures.CompactSupportFiniteProjection.originSupportComparison_composition`
  (`lem-sf-finite-support-origin-binary-normalization`): a tensor-free normalization
  equation for two support operations and the canonical origin compositor.

Thus 1 hole was closed and 2 were added; this is a decomposition, not a net proof count.
There is no direct sorry in the item or in any definition or private declaration.
The first remaining statement has no arbitrary-compactification or pentagon conclusion;
the second has neither a projection component nor a triple-composition conclusion.

## No longer needed

No public or proof import was removed from the original item; no module is withdrawn.
The extracted naturality module omits the parent's unused imports
`Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`,
`Sheaf.Paper.IntrinsicTorAmplitudeTransport`,
`Sheaf.Paper.ConstructibleEtaleModuleSheafComparison`, and
`WeilConjectures.SixFunctors.ProEtale.Derived.ProjectionFormula`; its sole import is
`ConstructibleProjectionMates`. An unused private fixed-component comparison was also
omitted from the extraction.
The whole-datum wrapper `Sheaf.SixFunctors.ProjectionCompatibleTriangleAssembly`
(node `lem-sf-projection-compatible-triangle-assembly`) is not needed by this reduction:
the finite-stage geometric step uses the compatible-triangle theorem and the general
`cartesianCompactSupportCompositor` and `compositionProjectionMate` statements directly.
The latter two nodes, the ringed tensor-composition compatibility and finite-ring origin
are still needed in the lower statements; they have not been pruned. Canonical origin
composition and finite projection compactification transport also remain needed.
No blueprint unit statement or route is bypassed.

## Where the brief, the DAG or earlier work was wrong

The archived module's signature is usable and compiled unchanged before proof work.
The plan's wrapper triangle-assembly theorem takes a whole operation datum, while this
item has only a finite operation stage. Its raw compositor/projection lemmas are the
appropriate lower statements, as the current node's prose already anticipates. The plan
also omitted the naturality declaration required to transport the first compactification;
that argument existed privately in the parent, so it is reproduced in a lower proved
module rather than assumed or imported cyclically. No mathematical statement is disputed.

## New nodes

`lem-sf-finite-projection-binary-square`: projection composition only at a compatible
choice of first and composite compactifications; all inputs share those choices. Its
proper/open geometric proof is specified and left as a named theorem.

`lem-sf-finite-support-origin-binary-normalization`: binary support normalization in the
canonical origin category, with explicit origin inclusion and support comparisons. This
is the input from which the item's complete categorical calculation derives the pentagon.

`lem-sf-finite-projection-input-naturality`: the proved input-naturality argument extracted
from the parent's private proof. It concerns a single projection and has no composition law.

`lem-sf-finite-realization-etale-origin`: the proved property needed to corestrict inverse
coefficient realization to the full bounded-below etale-origin category. It chooses no
new object data.

No change record is needed: all interface additions are new modules with new nodes;
existing interfaces remain identical.

## Second reading by N4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
