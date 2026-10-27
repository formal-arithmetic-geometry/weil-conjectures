## What changed

Filled `AlgebraicGeometry.Etale.rightDerivedLowerShriekCompCoherence` by applying the existing
`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso`. Added its module,
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekCompositionCoherence`, as a private proof
import. The existential conclusion is definitionally the assigned proposition: unfolding
`RightDerivedLowerShriekCompCoherence` and `ProjectionCompCoherent` gives the existing
statement, including both compatibility clauses, all universes and all hypotheses.
No declaration signature, definition, attribute or public import was changed.

The import-direction checker accepts the added import. The complete assigned module compiles
through lcompile.py (exit 0, reported compiler time 9.1 seconds). Mathlib searches through
LeanSearch, Loogle and grep gave no relevant replacement; the existing source declaration
was found by searching the adopted source library. The unit record sk-prop-sf-cbc has no
realized statement or steps that this application bypasses. Its existing graph/coherence
argument remains attached to lem-route-exists-right-derived-lower-shriek-comp-iso.

## Proved and sorry left

Closed one of one local holes:
`AlgebraicGeometry.Etale.rightDerivedLowerShriekCompCoherence`.
Zero holes remain in the assigned module; zero holes were added; zero statements were split
off. This is a proof from an existing stated dependency, not a claim that the underlying
coherence argument is sorry-free. The existing dependency
`AlgebraicGeometry.Etale.exists_rightDerivedLowerShriekCompIso` still has its original hole
(node `lem-route-exists-right-derived-lower-shriek-comp-iso`); its module was not changed.

## No longer needed

None. No existing import, declaration, node or module was removed. The graph/projection/base-
change dependencies of the existing coherence theorem remain needed by that theorem's plan.
The assigned wrapper needs no new copies of those lemmas.

## Where the brief, the DAG or earlier work was wrong

The assigned file is present despite its rework row describing an adopted source missing
after rollback. Its original contents were copied and preserved except for the proof and
private proof import. No DAG node currently has this module as its Lean attachment, nor was
its theorem name found in dag/nodes. The mathematically identical existing source statement
is already attached to `lem-route-exists-right-derived-lower-shriek-comp-iso`; no new duplicate
statement or node is introduced. The existing DAG proof for that dependency is unchanged.

## Second reading by A3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
