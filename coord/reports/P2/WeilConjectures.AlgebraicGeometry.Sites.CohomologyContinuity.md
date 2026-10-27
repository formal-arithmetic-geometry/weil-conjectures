## What changed

Proved `AlgebraicGeometry.Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit`
from the three existing dependencies of
`lem-weil-pbc-grothendieck-cohomology-limit-vanishing`.
The underlying limit is compact by `Scheme.compactSpace_of_isLimit`; an affine projection
onto a quasi-separated stage makes it quasi-separated. Hypercover comparison identifies
derived sections with concrete hypercover cohomology at every stage and at the limit.
Stage vanishing and joint generation equate the identity and zero on limit hypercover
cohomology. The comparison isomorphism transports this vanishing to derived sections.

The retained elementwise theorem `cohomologyMap_isColimit_of_isLimit` exceeded the file
compile limit with its inline cohomology diagram and cocone construction. Its proof now
reuses `exists_cohomologyMap_preimage_of_isLimit` for class descent and the existing
`finiteStageKilling` helper for eventual vanishing. The latter is accessed by a private
`import all Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity`. Restriction to `Over i`
preserves the limit and the qcqs and affine hypotheses, and its resulting object supplies
the required later stage and arrow. This keeps the same class-descent and filtered-colimit
argument while reusing the existing constructions and their API.

Added private proof imports of `Mathlib.AlgebraicGeometry.AffineTransitionLimit`,
`Sheaf.AlgebraicGeometry.GrothendieckHypercoverComparison`,
`Sheaf.AlgebraicGeometry.GrothendieckHypercoverLimitGeneration`,
`Sheaf.AlgebraicGeometry.EtaleCohomologyContinuity`, and
`Sheaf.AlgebraicGeometry.FixedBaseCohomologyClassDescent`.
The elementwise theorem uses scoped backward elaboration options. No local attributes,
instance changes, new declarations, public import changes or signature changes are made.
The original abelian-group vanishing proof and all definitions are preserved verbatim.
The generic theorem follows its existing node's four steps, so its node needs no change.

## Proved and sorry left

Closed one of one holes:
`AlgebraicGeometry.Etale.isZero_rightDerived_sectionsFunctor_upperStar_of_isLimit`
(node `lem-weil-pbc-grothendieck-cohomology-limit-vanishing`).

Zero direct `sorry` left in the item; zero holes added; zero statements split off.
The existing elementwise and abelian-group vanishing theorems remain proved.

Validation: the complete final file compiled through `lcompile.py` in 42.3 seconds.
All public imports, theorem signatures, the definition body and the original abelian
vanishing proof were compared with the current source and preserved.

## No longer needed

Removed the direct private import
`WeilConjectures.AlgebraicGeometry.CofilteredFixedBaseCohomologyContinuity`.
It remains a dependency of the reused cocone theorem, so this does not withdraw or globally
prune that module or its node. No module is withdrawn.

All three generic proof dependencies are used:
`lem-weil-pbc-grothendieck-hypercover-model`,
`lem-weil-pbc-grothendieck-hypercover-comparison`, and
`lem-weil-pbc-grothendieck-hypercover-limit-generation`.
No declared generic dependency is pruned, and no new nodes are introduced.

## Where the brief, the DAG or earlier work was wrong

The existing module docstring says that the general coefficient vanishing form is not
formalised; that historical sentence is now outdated. Existing docstrings are preserved.
The generic DAG plan and its dependency declarations fit the proof without mathematical
correction or any change to the unit route.

The original retained elementwise proof timed out after 60 seconds. Reusing the existing
class-descent and finite-stage-killing results avoids the expensive inline construction;
no time limit is raised and no new lemma or file is split off to handle the timeout.

## Second reading by P2

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
