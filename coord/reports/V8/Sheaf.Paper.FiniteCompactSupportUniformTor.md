## What changed

Completed `finiteCompactSupport_uniformTor_after_denseRefinement` in
`Sheaf.Paper.FiniteCompactSupportUniformTor`, with its signature and both comparison
constructions unchanged. The proof follows the prescribed dense scheme-image,
dimension, open-extension, and proper-direct-image argument. It supplies all
finite-type and over-base instances explicitly, and uses the same dimension bound
for every positive coefficient level and every input interval.

For the retained comparison domain, the existing arbitrary-finite-ring theorem
`Scheme.finiteRing_constructibleDerived_origin` directly accepts the intrinsic input.
Finite cohomological support gives its boundedness hypothesis. The proof keeps a
bounded-below etale complex, takes its continuous-coefficient comparison image with
identity origin witness, and composes `refinementFixedWitnessIso` with the exact
realization composition isomorphism to obtain the required `w`. It then uses the
specified `finiteCompactSupportDenseComparison`, so the final comparison equality
is reflexivity. Constructibility transports by the existing isomorphism-closure
instance; Tor amplitude transports by composing each representative isomorphism
with the inverse comparison, keeping every resolution and every test module.

The node's proof, proof dependencies, and proof origin now describe these choices.
No signatures, public imports, definitions, consumers, or source-library modules
were changed. No new modules or nodes were introduced.

Validation: the final module compiled cleanly through `lcompile.py` in 6.0 seconds,
with no warnings. A source comparison checked that both comparison definitions and
the complete theorem signature are unchanged; all Lean lines are at most 100 characters.
The DAG proof dependency list is exactly the union of the proof steps' uses.

## Proved and sorry left

Closed the one original hole:
`AlgebraicGeometry.ProEtale.finiteCompactSupport_uniformTor_after_denseRefinement`
(node `lem-coef-finite-compact-support-uniform-tor`).

The item has zero remaining sorries. Added zero holes; split off zero statements.
This proves the item from existing declared dependencies, rather than decomposing it.

The dimension theorem includes empty schemes; the proof never chooses a point or
assumes a nonempty support. Bounds use `min` and `max`, so empty cohomological support
is covered. The proof also covers `d = 0`, `n = 1`, and `a = b` without extra
hypotheses. Extra components in the original compactification do not enter the
dimension estimate: it applies only to its specified dense refinement.

## No longer needed

Removed private imports `Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated` and
`Mathlib.AlgebraicGeometry.Morphisms.Immersion`: the retained boundary-preparation
public interface already supplies these geometric dependencies. Their DAG nodes
remain needed through the compactification's existing quasi-compactness and dense
scheme-image API; neither mathematical dependency is withdrawn.

Removed private import `Sheaf.Paper.ProEtaleConstructibleOrigin` and replaced its
planned use (`lem-sf-proetale-constructible-origin`) by the existing finite-ring
intrinsic origin criterion in `Sheaf.Paper.FiniteRingConstructibleDerivedOrigin`
(`lem-weil-pbc-finite-ring-constructible-derived-origin`). This is an existing generic
tool realizing exactly the same source step, without changing the unit route.
The latter module is already sorry-free in the current source. The maintainer may
record its generic tool approval; no approval was added by this packet.

Removed private import `Sheaf.Paper.CompactificationCoherence` and planned proof
dependency `prop-compactification-coherence-detailed`. The item already defines the
required objectwise canonical comparison using `refinementComparisonAtWitness` and
normalized realization comparisons. Its statement requires that value, rather than
the global naturality/common-refinement/cocycle assertions. The definition nodes
`def-sf-refinement-comparison-isomorphism` and
`def-sf-intrinsic-compact-support-realization` now explicitly occur in proof step 6.
The two obsolete top-level tool approvals were removed, preserving the others in
order. These modules may still be needed elsewhere; no library-wide withdrawal is
claimed and no files were deleted.

## Where the brief, the DAG or earlier work was wrong

The original plan was mathematically sufficient. Its origin lemma uses a different
coefficient presentation; the existing finite-ring essential-image criterion is a
shorter interface for this intrinsic input. The global compactification-coherence
statement is stronger than the objectwise comparison required here: that comparison
was already constructed in the item before this proof. Neither point changes the
statement or the dense/open/proper route of the source paragraph.

## Second reading by V8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
