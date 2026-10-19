## What changed

Proved `AlgebraicGeometry.Etale.canonicalDerivedPullbackCompositionMonoidal` in
`Sheaf.AlgebraicGeometry.DerivedPullbackCompositionMonoidal` using the existing source-library
coherence API. Added proof-only imports of
`WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.CompUnit` and
`WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionMonoidal`.
A proved private helper performs the tensor-composition conversion over a general coefficient
category before specialization to modules. The local symmetric-to-braided instance priority
keeps the concrete module coefficient instance aligned with that generic API.
All existing public imports and the theorem's written signature are preserved.
The declaration docstring and the node's proof, proof_deps and proof_origin now describe this route.

## Proved and sorry left

Closed 1 original hole:
`AlgebraicGeometry.Etale.canonicalDerivedPullbackCompositionMonoidal`
(node `lem-kun-derived-pullback-composition-monoidal`).
Added 0 holes; split off 0 statements. No `sorry` remains in the delivered Lean module.
The private helper `derivedPullbackCompositionTensor` is proved.

Validation on the resumed attempt: the delivered module compiles cleanly through
`lcompile.py` in 11.2 seconds. A separate scratch theorem repeats the original signature
without the local instance-priority setting and applies the delivered theorem successfully;
the elaborated statement is therefore preserved. The axiom check includes `sorryAx`
from existing dependencies, so this closes the assigned proof hole without claiming
a transitively sorry-free result. Both added imports pass the import-cycle check.

## No longer needed

All six original public imports are preserved: they supply statement-level definitions,
coefficient instances, or comparisons appearing in the unchanged theorem. Both new imports are
used only by the proof. Relative to the current shared source, the following nine proof-only
imports are removed because the source coherence API supplies the required equations directly:

- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`
- `Sheaf.AlgebraicGeometry.PullbackConstantModule`
- `Sheaf.CategoryTheory.Sites.InverseImageBilinearAdjunction`
- `Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`
- `WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`
- `WeilConjectures.SixFunctors.Etale.Derived.Tensor`
- `WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison`
- `WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`

The last three remain available transitively through the preserved public imports; their
redundant direct imports are unnecessary. The following old proof dependencies are bypassed by the already proved source-library coherence
results; they are removed from this node's proof_deps (statement dependencies are unchanged):

- `def-pc-fibre-product`
- `lem-cat-right-adjoint-composition`
- `lem-kun-pullback-constant`
- `lem-sfb-site-inverse-image-bilinear-adjunction`
- `lem-weil-pbc-exact-functor-derived-factorization`
- `lem-weil-pbc-inverse-image-composition`
- `lem-weil-pbc-inverse-image-composition-module-linear`
- `lem-weil-pbc-ringed-topoi-derived-tensor-pullback`
- `lem-weil-pbc-site-derived-tensor-descent`
- `prop-weil-pbc-inverse-image-modules-exact`

In particular the proof does not import
`Sheaf.CategoryTheory.Sites.InverseImageBilinearAdjunction`,
`Sheaf.AlgebraicGeometry.EtaleInverseImageCompositionModuleLinear`,
`Sheaf.AlgebraicGeometry.PullbackConstantModule`,
`Sheaf.Paper.RingedTopoiCanonicalTensorPullbackOfUniverses`, or
`Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`.
Their representative-level tensor, bilinear-adjunction, constant-section and localization
arguments are already implemented by the source-library theorems used here.
This is pruning of this proof route, not a claim that those modules have no other consumers.
The unit record `sk-thm-sf-compatibility` has no realized statement or step at this node;
its six-operations compatibility route is preserved.

## Where the brief, the DAG or earlier work was wrong

The planned seven-step representative calculation is unnecessary because the source library
already proves every displayed compatibility for these very canonical comparisons. No mathematical
statement is disputed or changed. The concrete module tensor instance needs a generic-coefficient
helper and explicit tensor-bifunctor normalization when applying the existing tensor equation.
No definition, consumer module, target statement or public visibility is changed.

The dry-run checker conservatively requires an interface change record for the local instance
priority command. The command is local, and the separate importing signature check compiles
without it, so consumers need no edits. The record is
`coord/changes/derived-pullback-composition-local-instance.md`; it lists the transitive source
consumers and their holders. The consumer-list tool's process was killed by the environment before producing a result;
the table was independently checked from the transitive closure of the source imports. This
incident did not affect remote compilation or the completed first delivery preflight.

## Second reading by E4

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
