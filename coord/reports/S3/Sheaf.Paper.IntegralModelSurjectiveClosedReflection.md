## What changed

Replaced the hole in `AlgebraicGeometry.ProEtale.integralModel_surjective_closed_reflection`
by a proof using the existing cover-refinement and condensed-module equivalence interfaces.
Proved private comparison helpers handle any commutative condensed coefficient ring. They compare
models pulled back from the point using `Functor.mapModCompIso`, then cancels extension
and restriction of scalars along the canonical coefficient isomorphism. The forward
implication base changes the cover. The reverse implication refines the cover, transports
each model isomorphism to the closed fibre, and lifts it using full faithfulness.

## Proved and sorry left

Closes `AlgebraicGeometry.ProEtale.integralModel_surjective_closed_reflection`
(node `lem-sfb-integral-model-surjective-closed-reflection`): 1 of 1 original holes.
No holes added. No `sorry` remains in any delivered module.
The proof uses existing declarations whose own transitive proof obligations remain with
their existing nodes; it introduces no new obligation.

## No longer needed

Removed proof imports `Sheaf.AlgebraicGeometry.ProEtaleInverseImage`,
`Sheaf.CategoryTheory.SiteInverseImageTensor`, and
`WeilConjectures.AlgebraicGeometry.Morphisms.UniversalHomeomorphism`.
Also removed the proof-only imports `Sheaf.Paper.CartesianCoefficients`,
`WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars`, and
`WeilConjectures.SixFunctors.ProEtale.ModuleObject.UpperLowerStar.Defs`; their
declarations are already re-exported by the public imports used by the module.
The corresponding nodes `def-weil-proetale-inverse-image`,
`lem-weil-pbc-left-exact-site-inverse-image-tensor`, and
`lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism` are not needed
by this proof. Nor is `sk-prop-sfb-cartesian-coefficients`: the generic monoidal
point comparison already supplies the coefficient map used here. These nodes may
remain needed by other modules. Retained `sk-def-sfb-change-of-scalars`,
`sk-def-sfb-module-pushforward-pullback`, the cover-refinement and condensed-equivalence
nodes, and added the existing `sk-def-sfb-pullback-from-point-comp` to the proof record.
Removed the obsolete top-level `tool_uses` approvals for
`lem-weil-pbc-left-exact-site-inverse-image-tensor`,
`lem-weil-pbc-surjective-closed-immersion-universal-homeomorphism`, and
`sk-prop-sfb-cartesian-coefficients`; the two retained approvals keep their order.
No blueprint unit statement or realized step is bypassed.

The local transparency attributes are documented in
`coord/changes/integral-model-surjective-closed-reflection-proof-transparency.md`.

## Where the brief, the DAG or earlier work was wrong

The current finite-constant-model definition already represents a model as the inverse
image of a finitely presented condensed module on the point. Thus its pullback comparison
is obtained directly from the existing module-functor composition and scalar-change
isomorphisms. Reconstructing the constant-sheaf tensor coequalizer is unnecessary.
The proof allows the scalar module to vary with the covering index, preserves its original
finite presentation, and uses no freeness, nilpotence, or Noetherianity assumption.
The empty cover and zero model are allowed by the same argument.

The final single-file compile passed without warnings in 2.9 seconds. Directly passing
chosen scheme pullback projections into the dependent coefficient-functor types caused
kernel conversion timeouts. The proved `exists_pullback_cover` interface provides the
same pullback cover, index map, refinement maps, and commuting equations as existential
witnesses. Applying the model comparisons to those abstract witnesses removes that
expensive conversion. No existing definition, statement, or compile limit changed.

## Second reading by S3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
