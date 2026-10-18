## What changed

Proved `AlgebraicGeometry.nagataMorphismEqEventually` in
`Sheaf.AlgebraicGeometry.NagataMorphismEqEventually`, preserving its signature and all imports.
Two proved private helpers express functoriality of global sections and equality of maps to an
 affine scheme from equality on the base-ring image and the chosen generators.

The proof follows the existing DAG and the current blueprint: membership in the finite stage
set gives bounds on every lambdaJK and mu via `le_directedFiniteUpperBound`; applying
`nagataQCOpenEqEventually` shows that the inverse images of the U charts cover the source.
For each generator, an explicit pullback lift maps the transported open to its coefficient
witness stage; applying global sections to that lift transports `coefficientEquality`.
The chart maps agree over T by cancellation of the open immersion T → S and the recorded
`chartOver`, `overPhi`, `overPsi`, `hphi`, and `hpsi` equations. Ring-hom extensionality on
`Subring.closure` gives equality on the affine target chart. Open-cover extensionality and
`pullback.hom_ext` finish the global equality.

Validation: the final module compiled cleanly through `lcompile.py` in 5.7 seconds, with
no warnings and no occurrences of `sorry`. All lines have at most 100 characters.
No definition, public signature, DAG route, or consumer module changed.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.nagataMorphismEqEventually`
(node `lemma-nagata-morphism-eq-eventually`).
Added 0 holes; split off 0 theorems. No `sorry` remains in the delivered module.
The two new private helpers, `comp_appTop_apply` and `hom_eq_of_generators`, are proved.
As intended in stage 3, the proof uses the existing declarations
`nagataQCOpenEqEventually` and `le_directedFiniteUpperBound`; their existing holes are
unchanged and belong to their own nodes and modules.

## No longer needed

None of the original imports, proof dependencies, nodes, or modules is pruned: all three
stated dependencies are used. The temporary explicit imports of
`WeilConjectures.Mathlib.AlgebraicGeometry.Gluing` and
`Mathlib.Algebra.Ring.Subring.Basic` were removed after compilation confirmed the necessary
APIs are already available through the existing public imports. No new import is delivered.

## Where the brief, the DAG or earlier work was wrong

No mathematical defect found. The existing declarations supply exactly the needed data.
The proof does not require new intermediate statements or a change of route, so no node
copy or change record is necessary. Empty chart-index or generator types require no extra
nonemptiness hypotheses: the cover equations and closure generation statements handle them.

## Second reading by B9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
