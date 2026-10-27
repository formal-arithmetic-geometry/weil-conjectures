## What changed

Prove `AlgebraicGeometry.Scheme.adicFiniteGradedLayer_residueTensor` in
`Sheaf.Paper.AdicGradedResidueTensorComparison`, with its statement unchanged.
Private proved helpers construct constant realization versus scalar restriction,
package the existing ordinary tensor cancellation as a natural isomorphism,
and compute the derived comparison on one K-flat representative over the larger
quotient. The final composition uses the existing `adicFiniteRho` isomorphism.
All preceding algebraic declarations remain unchanged.
The complete module passed `lcompile.py` without warnings in 13.8 seconds;
all temporary profiling options were removed before that compile.
Proof-only imports provide K-flat resolution, arbitrary K-flat change of rings,
ordinary cancellation, single-tensor computation, and the existing scalar
restriction computation. Update only this module's node to record this route.

## Proved and sorry left

Close the one original hole:
`AlgebraicGeometry.Scheme.adicFiniteGradedLayer_residueTensor`
(node `lem-sfb-adic-graded-residue-tensor-comparison`).
Zero holes remain in the item, and zero holes are added anywhere.
This is a proof from existing declarations, not a decomposition.

## No longer needed

No existing import or module is withdrawn. All six original proof dependencies
remain used, and `lem-sf-ringed-kflat-single-tensor-comparison` is additionally
used for its existing K-flat single-module computation. There are no new nodes.
The route does not need an A-coefficient K-flat representative, a second
resolution of the graded constant module, termwise flatness, constructibility,
Noetherianity, completeness or boundedness for the comparison. The independent
K-flat change-of-rings theorem applies directly to the first representative.

## Where the brief, the DAG or earlier work was wrong

The original plan is valid but longer than necessary: resolving N_(n+1) over
B=A/J^(n+2), and then using repeated reduction, avoids doing parallel A-to-B
and A-to-C representative computations. The existing K-flat single-tensor
comparison supplies the exact one-sided computation with the constant module,
so that module need not be resolved here. Constant realization versus scalar
restriction needs a concrete comparison; its proof is included, using the
sheafification adjunction and local bijectivity of both underlying units.
The source read is Stacks proetale.tex, Tag 09BR,
lemma-compare-truncations-constructible, and sites-cohomology.tex, Tag 06YU,
definition-derived-tor and its preceding construction. The unit route stays.

## Second reading by Y3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
