## What changed

Proved `AlgebraicGeometry.ProEtale.integralReduction_underlying_directImage` with its
original signature. The proof uses the existing normalized finite scalar pullback,
scalar-cone comparison and integral reduction tower. Mate uniqueness, the triangle
five lemma and reflection by exact faithful restriction establish the projection
isomorphisms required by the tower theorem.

Proved the underlying abelian comparison in private helpers. Nonzero integer
multiplication is injective on continuous integral coefficients, and exact inverse
image preserves this monomorphism. Evaluating shows every coefficient section is
torsion-free over Z, hence flat. Sheafification of the sectionwise tensor proves
flatness of the actual integral coefficient sheaf. The free module functor is
therefore exact, so its right adjoint (forgetting the action) preserves K-injective
complexes. The two standard derived-composition isomorphisms now derive the literal
underived forgetful/direct-image square.

Validation: the server compiled the complete assigned module without warnings
in 15.9 seconds. The theorem signature and original public imports are byte-identical
to the source; the changed DAG dependency graph has no cycle through this node.

Only the assigned Lean module and its DAG proof are changed. No public definition,
theorem signature, target, source-library declaration or consumer is changed.

The reduction normalization, cone and tower nodes are tools from unit
`sk-thm-sf-pf-adic`: their positive uniformizer quotient comparison supplies exactly
the finite perfect-coefficient step of `sk-prop-int-compactness`. The unit's compactness,
proper direct image and direct-sum route is retained. Generic exact-adjoint and
derived-composition results are existing proved tools. Maintainer approval of
cross-unit tool uses is left to the maintainer; no `tool_uses` is added here.

## Proved and sorry left

Closed the original one hole:
`AlgebraicGeometry.ProEtale.integralReduction_underlying_directImage`
(node `lem-sfb-integral-reduction-underlying-direct-image`).

Added zero holes and zero split-off statements. The assigned module has zero
remaining `sorry`. All private helpers are proved.

The proof uses the existing statements
`integral_reduction_pullback_normalization`,
`integral_direct_image_reduction_cone`, and
`integral_direct_image_reduction_tower`; their pre-existing holes remain in their
own unchanged modules. This delivery proves the assigned statement from those
stated dependencies, as required by stage 3.

## No longer needed

The direct dependency `lemma-weil-pbc-perfect-projection-formula` and its module
`Sheaf.Paper.PerfectProjectionFormula` are not used.
The positive quotient is handled by the existing scalar-cone comparison instead.
This removes a direct DAG dependency; it does not withdraw that module or claim
that other consumers no longer need it.
The two-term resolution remains needed through that cone theorem; its node is
not withdrawn. No library module or declaration is deleted.

No bounded-below acyclic-resolution, module Cech or constructibility comparison
lemma is needed: flat integral coefficients give a comparison on unbounded derived
categories. No new finite quotient presentation, ringed-topos transport, or
additional proof obligation is introduced.

## Where the brief, the DAG or earlier work was wrong

The original proof plan was mathematically usable, but its Cech comparison need
not be developed for this item. The stronger unbounded forgetful comparison follows
from torsion-freeness of the actual integral coefficient sections and the exact
free/forgetful adjunction. The original boundedness and quasi-compact/quasi-separated
hypotheses remain verbatim although the new argument does not use them.

The finite reduction is the positive quotient of exponent n+1 throughout. The
argument includes n=0, zero complexes, empty test objects and empty schemes.
No statement is disputed or weakened.

## Second reading by C4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
