## What changed

Restored the quarantined module
`Sheaf.AlgebraicGeometry.PerfectLocalModelsStageComparisons` at its original
library path. Its archive and its DAG attachment are preserved. Replaced its
public import of the empty, withdrawn `Sheaf.AlgebraicGeometry.DerivedPullback`
with `WeilConjectures.AlgebraicGeometry.DerivedPullback`, which actually declares
the functor in the unchanged public signature. Added a private import of
`WeilConjectures.AlgebraicGeometry.OpenSectionsCohomologyModel` for the existing
cached abelian structures used by the archived proof's local instance command.

Fixed elaboration by passing the existing shared derived-category instances
explicitly and naming the transition and gluing applications before destructuring
them. Locally prioritize the existing exact-restriction instances, keep
`Scheme.Opens.toScheme` irreducible, and make the two proof declarations respect
transparency. This avoids thousands of repeated reductions of chosen scheme
limits and localized derived functors. No definition, theorem signature,
universe, mathematical hypothesis, or conclusion changes. The heartbeat budgets
are lower than in the archive, and the file timeout remains 60 seconds.

The restored proof uses all four declared proof dependencies: descended transition,
derived object gluing, pullback perfectness, and local perfect-model transport.
The proof and proof_deps already describe this route accurately, so the DAG does
not need a route update. The unit's own statement and realized steps are retained.

Change record:
`coord/changes/PerfectLocalModelsStageComparisons-restoration.md`.

## Proved and sorry left

This is a zero-hole compile repair: the archived item had 0 sorries, and the
restored item has 0 sorries. Holes closed: 0. Holes added: 0. Split off: 0.

`AlgebraicGeometry.perfect_local_models_stage_comparisons` is proved, with its
original signature preserved byte for byte and matching the node's Lean record
(`lem-pc-perfect-local-models-stage-comparisons`). Both private helpers,
`perfect_of_two_open_models` and `glue_perfect_two_open_models`, remain proved.
No declaration with sorry is delivered. This does not claim closure of all
transitive proof dependencies.

The single-file compile succeeds within the unchanged time limit. The delivery
preflight additionally checks every declaration's axioms and direct holes.

## No longer needed

Removed the public import of `Sheaf.AlgebraicGeometry.DerivedPullback`, an empty
withdrawn module, replacing it by the adopted source-library module that carries
the same notion. No mathematical dependency, node, or module is pruned. All four
recorded proof dependencies are used. The stage-gluing parent remains dependent
on this module, including while that parent is quarantined.

## Where the brief, the DAG or earlier work was wrong

The active item file was absent because of its rework quarantine, not because its
mathematics had been withdrawn. The rework row was read before copying the
archive. Its complete proof no longer compiled: `derivedPullback` was not
publicly imported, and `openComparisonModuleAbelian` was not visible. Simply
restoring its bytes would therefore fail again. The repaired import environment
exposed an elaboration bottleneck at the transition/gluing application; explicit
instances and named applications repair it without a new lemma or a split.

Searches with LeanFinder returned scheme-gluing constructions, Loogle returned
generic functor/isomorphism lemmas, and the service grep returned no direct match.
Local library searches found the four existing declarations used by the proof;
there is no shorter matching theorem that replaces them. Read the local Stacks
proof of `lemma-descend-perfect` (Tag 09RF), especially the overlap isomorphism and
application of the two-open gluing lemma. The proof route remains that argument.
Empty schemes, empty overlaps, equal opens, and non-strict directed preorders
require no added hypotheses.

`tools/downstream.py` cannot index the absent item. Searching both active Lean
sources and quarantine finds the archived `PerfectLocalModelsStageGluing` as its
only consumer; its explicit call still has the same name, binders and universes.
The parent node also retains this dependency. No consumer adaptation is necessary.
The blueprint's current text places the old semicontinuity sketch inside
`sk-thm-picard-perfect`; no blueprint or unit record is edited.

## Second reading by B2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
