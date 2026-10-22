## What changed

Wrote a proof of
`AlgebraicGeometry.ProEtale.CondensedRing.locallyClosedGeneratorTensorIntersection`
from the existing library declarations. The six existing public definitions and the theorem
statement are unchanged. All added helpers are private and proved in the item module.

The ordinary comparison is reconstructed from support on the actual scheme fibre product.
Restriction normalizes it, and injectivity on Hom sets proves naturality and compatibility
with every normalized change of factorization. Flatness of the extended lisse modules is
proved by detecting kernels on their support. The K-flat single-complex comparison then
identifies derived tensor with ordinary tensor, naturally in both inputs. A common refinement
of the two lisse covers gives the rank-product trivialization. Homology, constructibility and
vanishing on arbitrary disjoint pullbacks follow from the resulting single complex and a
closed-then-open factorization of the intersection.

Proof imports give access to the existing generic support, local-freeness, constructibility
and K-flat APIs, including proved private helpers through `import all`. Updated the item's
DAG proof, proof dependencies and proof origin to describe this route. The unit route is
unchanged; its `realized` record is empty.

The complete module compiles cleanly through `lcompile.py` in 35.3 seconds with normal
compiler settings, no warnings and no temporary diagnostics. The final assembly passes the
actual tensor functors as parameters and transports along proved whole-functor equations,
avoiding repeated comparison of expanded derived monoidal data. All six original public
definitions, their bodies, public imports and the theorem signature are unchanged.

The proof-local commands are recorded in
`coord/changes/E8-generator-tensor-proof-local-commands.md`. No consumer adaptation is needed.
The revised node's 23 proof dependencies were checked for paths back to this item; none exists.

## Proved and sorry left

Closed the sole original hole:
`AlgebraicGeometry.ProEtale.CondensedRing.locallyClosedGeneratorTensorIntersection`.

Proved 1 of 1 original holes; zero holes remain in the item. Every added helper is private
and proved. Zero holes, split statements, modules or axioms were added elsewhere. This is a
proof, not a decomposition. It uses existing library declarations as permitted by stage 3.

## No longer needed

Removed direct proof imports:

- `Sheaf.AlgebraicGeometry.CondensedSupportProjectionFormula`
- `Sheaf.AlgebraicGeometry.LocallyClosedExtensionCoherence`
- `Sheaf.Paper.FlatSingleScalarConventions`
- `Sheaf.AlgebraicGeometry.CondensedPullbackTensorComparison`
- `Sheaf.AlgebraicGeometry.CondensedOpenClosedInternalHomMaps`
- `Sheaf.AlgebraicGeometry.ProEtaleRingSheafOperations` (already public through the mates module)

The revised proof does not use these old proof dependencies:

- `lem-weil-pbc-noetherian-open-subscheme-noetherian`: the embedding/local-finite-type
  argument handles all immersions uniformly.
- `lem-weil-pbc-closed-immersion-proper`: properness is unnecessary.
- `def-sfb-condensed-pullback-tensor-comparison`: use the existing monoidal inverse-image API.
- `lem-sfb-flat-single-scalar-conventions`: the calculation remains in module objects throughout.
- `lem-sfb-condensed-support-projection-formula`: use ordinary support reconstruction and flatness.
- `lem-sfb-locally-closed-extension-coherence`: prove the needed full faithfulness and normalized
  comparison directly from open and closed adjunctions. Its old statement dependency is preserved.
- `def-sfb-open-closed-internal-hom-comparisons`: no internal Hom comparison is needed.
- `lem-sp-exact-functor-preserves-homology`: transport homology along the single-complex comparison.

Removed the old `tool_uses` entries for those dependencies. No source-library declaration or
module is removed. These are dependencies unnecessary for this proof, not claims that their
other consumers disappear.

## Where the brief, the DAG or earlier work was wrong

The original projection-formula route is mathematically valid. Its sectionwise ringed-module
interfaces require coefficient and convention transports that the support reconstruction
argument avoids. The replacement proves the unchanged statement, including both factor orders,
the actual unreduced fibre product, zero ranks, arbitrary condensed coefficients, and arbitrary
sources for the final disjoint-pullback vanishing.

The new generic tools used below the unit level are the support-reconstruction helpers,
abelian closed support/counit, the refinement helpers in `FiniteEtaleLocallyFreeModels`, and
the stratification helpers in `CoefficientHeartLisseExtensionConstructible`. Only those generic
parts are used; neither the finite-etale pushforward theorem nor the coefficient-heart
generation theorem is invoked. The source library's canonical single-tensor construction and
its K-flat localization comparison supply the derived calculation.

## Second reading by E8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
