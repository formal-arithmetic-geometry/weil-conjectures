## What changed

Proved `AlgebraicGeometry.Scheme.exists_strictHenselization_limit_smaller_dimension`
in `Sheaf.AlgebraicGeometry.StrictHenselizationLimit`, preserving its signature. The proof
uses the existing models, the residue-field transcendence-degree tower theorem, and the
closed-irreducible dimension theorem. Two proved private helpers handle the field towers
and the dimension contradiction. The connected slice forgetful functor preserves the limit.

In the unclaimed `Sheaf.AlgebraicGeometry.StrictLocalAlgebraicResidueModels`, exposed the
transition compatibility with its individual maps to Spec L, proved for the existing
coefficient-subalgebra inclusions. The construction and every old conclusion remain.
The change record is `coord/changes/strict-local-model-transition-compatibility.md`.
Both DAG nodes now describe the formal proof. No new module or node was introduced.

Added proof imports `WeilConjectures.PointCount` (canonical residue-field algebra maps)
and `Mathlib.CategoryTheory.Limits.Constructions.Over.Connected` (limit preservation).
The finite-type dimension and point-closure comparison modules already imported supply
the remaining general tools. All compilation uses lcompile.py, one file at a time.

Searches: LeanFinder for strict henselization inverse limits and smaller dimension returned
only generic Henselian/finite-dimension facts; Loogle for Algebra.trdeg found the tower API;
msearch grep for trdeg/topologicalKrullDim found no combined shortcut. Direct source
search found the existing chain-to-point-closure lemma used to shorten the last step.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Scheme.exists_strictHenselization_limit_smaller_dimension`
(node `lem-kun-0f0u`). Both private helpers are completely proved.

The repaired `AlgebraicGeometry.Scheme.exists_strictLocal_algebraicResidue_models`
(node `lem-kun-strict-local-algebraic-residue-models`) had zero textual holes and still has
zero; its additional compatibility clause is proved. No holes were added or split off.
There is no sorry left in either delivered Lean module. Existing dependencies may still
rest on other project holes; this delivery does not claim their transitive closure is closed.

## No longer needed

Removed proof import `Sheaf.AlgebraicGeometry.FiniteTypeResidueTrdeg` and dependency
`lem-kun-finite-type-residue-trdeg`. The proof needs positivity of trdeg_K L and the finite
natural dimensions of the two point closures, not a separate finiteness proof of trdeg_K L.
No other original dependency or public import was removed. No other module is withdrawn.
The argument avoids an explicit global N-a bound: a hypothetical chain of length dim X
already contradicts the positive residue transcendence degree. This keeps the unit route.

## Where the brief, the DAG or earlier work was wrong

The old model theorem did not expose that transition maps commute with p_i, although
the node plan and target assembly assumed such compatibility. Individual maps p_i do not
by themselves define a diagram over L. The additional clause is proved from the existing
construction, with its full statement-change/citer audit in the model node and change
record. The other current consumer imports the module but has no call to the theorem,
so no consumer adaptation is required. Both DAG citers continue to hold.

The final bound can be obtained with the already proved point-closure chain lemma,
instead of constructing the chain supremum a second time. No mathematical source error
or unit-route departure was found. The model compatibility was checked also when b=0;
the strict dimension argument uses the original positive-transcendence-degree hypothesis.

## Second reading by R2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
