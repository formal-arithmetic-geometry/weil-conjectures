## What changed

Filled all seven proof holes in `Sheaf.AlgebraicGeometry.EtaleStalkTensorScalar`, preserving
all existing statement signatures. The tensor proof uses Mathlib's strong monoidal fiber
functor, compatibility with sheafification, and the colimiting tensor cocone. Naturality,
associativity, braiding, and the unit diagrams follow from those structures.

Scalar existence uses the already proved arbitrary-ring construction in
`Sheaf.Algebra.Category.ModuleCat.RingScalarExtension`. The component comparison is the
composite of the existing colimit and sheafification comparison isomorphisms. Its germ
formula and uniqueness follow from unit naturality, the adjunction, and colimit hom_ext.
Whiskering constructs the natural transformation. For iteration, sheafify the extended
sheafification unit, invert the resulting isomorphism, and compose with sheafification of
the specified `leftAdjointUniq` map. Check the stalk square on coprojections.

Added two proved private calculation helpers. Added proof-only imports for scalar extension,
left adjoints preserving sheafification, and the lax braided sheaf inclusion. Replaced the
broad stalk-monoidal import by the smaller monoidal instance imports. Updated the existing
DAG node's proof, proof dependencies, and proof origin to describe the implemented argument.
The public-import change record is
`coord/changes/K1-etale-stalk-tensor-scalar-imports.md`; both original direct consumers
compile unchanged, with no consumer adaptation.

## Proved and sorry left

Closed all seven original holes, in namespace `AlgebraicGeometry.Scheme`:

- `etale_stalk_tensor_unique`
- `etale_stalk_tensor_natural`
- `etale_stalk_tensor_coherence`
- `etale_scalar_extension_exists`
- `etale_stalk_scalar_unique`
- `etale_stalk_scalar_component_unique`
- `etale_stalk_scalar_iteration`

Zero sorries remain in the delivered module. Zero holes and zero split-off obligations
were added. A remote compile of the final module passed, and `#print axioms` for each
of the seven declarations lists exactly `propext`, `Classical.choice`, and `Quot.sound`.
Text comparison also confirms that all seven theorem signatures are unchanged. Both direct
consumers, `Sheaf.Paper.LisseTensorScalarExtension` and
`Sheaf.AlgebraicGeometry.FiniteEtaleTwistLine`, compile unchanged against this module.
The unchanged statements cover arbitrary schemes, zero modules and rings,
and noncommutative scalar rings; the proofs add no finiteness or flatness hypotheses.

## No longer needed

Removed the public import
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.StalkMonoidal`. Its geometric pullback
machinery is unnecessary for these proofs: the Mathlib point functor and the existing
Grothendieck-abelian monoidal instances suffice. This is pruning of this module's import
route; other parents can still import that module independently.

Removed `def-weil-pbc-geometric-stalks` from proof dependencies, while keeping it among the
statement dependencies. Its separate Lean module
`Sheaf.AlgebraicGeometry.PointedEtaleStalk` is not needed: the module coefficient categories
have the colimits required by Mathlib's point fiber functor directly. The sheafification
and cofiltered-neighborhood Mathlib leaves remain used. No library file is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original DAG omitted the existing arbitrary-ring scalar-extension construction from
its proof dependencies. Added `def-pod-ring-scalar-extension` and used its proved
`ringExtendScalarsAdj`, rather than constructing a new balanced tensor. The generic Mathlib
monoidal and colimit interfaces implement the planned germ arguments without introducing
new intermediate obligations. No statement or definition repair was necessary.

## Second reading by K1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
