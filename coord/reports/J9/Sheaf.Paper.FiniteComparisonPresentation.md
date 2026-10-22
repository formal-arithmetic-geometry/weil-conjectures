## What changed

The assigned module proves the unchanged `AlgebraicGeometry.ProEtale.finiteComparisonPresentation` by comparing the two coefficient presentations separately. Private helpers compare finite local models directly through covering sieves and weakly etale slices, globalize finite strata on qcqs schemes, compare the explicit internal realization with the common finite-discrete encoding, and transport the tensor tests and cohomological bounds through the specified equivalences.

The section functor monoidal structure uses Mathlib’s `Functor.CoreMonoidal.mk'`
with the tensor and unit isomorphisms and coherence supplied by the existing proved
public `internal_section_tensor_comparison` theorem. A private proved `Nonempty` lemma extracts the ordinary monoidal structure before
selection, so elaboration uses a small interface. The finite-Tor argument needs
existence of this coherent structure. No private tensor-comparison
implementation declarations are imported. A generic proved section/scalar/constant composite lemma assembles the inverse tensor
structure before specializing to the scheme. The inverse-equivalence transport is
also applied through a proved generic existence interface. Generic private
transport helpers keep the concrete adjunction and inverse-equivalence terms out of
repeated monoidal instance elaboration. A generic scalar-restriction helper selects only
the normalized ordinary monoidal projection of the existing tensor-transport theorem.
The inverse functor uses the named `scalarRestriction` API, and a local fixed-size
module-limits instance supports the counit comparison already at its signature. The constant internal module functor is built
explicitly on presheaves, with its scalar action given componentwise, before applying
sheafification. Its comparison with ordinary constant sheaves uses this action API
instead of unfolding an identity scalar restriction through transported ring objects.
The constructibility argument reuses the proved public
`HasFiniteConstantLocalModel.isLocallyFinitelyPresented` theorem.

The proof instances are explicitly local. The enclosing private section and the
final theorem use scoped attributes only. The consumer and command-context review
is recorded in `coord/changes/J9-finite-comparison-presentation-proof-context.md`.

Every original public import and the theorem signature are preserved. All additional helpers are private and proved. No upstream module or other group's module is changed.

The existing `ringIso_tensor_transport` theorem provides its normalized ordinary
comparison to prove existence of a monoidal structure on scalar restriction. The
generic proof constructs the required derived-category instances internally; its
small interface exposes only proved ordinary monoidal existence. These structures
serve the finite-Tor proof. Two private imports expose transitive instance names so
the helper can exclude their undetermined max universes locally and supply the same fixed-size
sheafification and locally bijective instances.

## Proved and sorry left

Closed the original hole in `AlgebraicGeometry.ProEtale.finiteComparisonPresentation`
(`lem-ctf-finite-comparison-presentation`): 1 of 1 holes closed. Holes added: none.
Holes remaining in the item: none. Split-off statements: none.

Tensor transport uses the existing `SheafOfModules.ringIso_tensor_transport` declaration.
The complete proof passed a single-file compiler check. The delivery's required
compile and preflight check the complete packet before pushing.

## No longer needed

The proof does not use `lem-weil-pbc-constant-coefficient-local-models-comparison`, `lem-weil-pbc-etale-stratification-local-gluing-core`, or `lem-sfb-coefficient-finite-local-systems-pullback`. It instead uses the generic affine-local finite-stratification argument from `NoetherianGlobalConstructibility`, actual constant-sheaf pullback comparisons, and finite presentations under the common encoding. These are dependency-route removals only; no module or declaration is withdrawn.
The corresponding unused dependencies are
`Sheaf.Paper.ConstantCoefficientLocalModelsComparison`,
`WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore`, and
`Sheaf.CategoryTheory.CoefficientFiniteLocalSystemsPullback`.
The private proof import `Sheaf.Paper.ConstructibleCoefficientSerre` and dependency
`lem-weil-constructible-coefficient-serre` are also no longer needed. The terminal
covering-sieve argument is proved directly from `finiteModels_over` and the weakly
etale slice equivalences. This avoids exposing the unrelated private cohomological
dimension imports of the Serre module; those adopted source declarations remain
unchanged. The tensor-comparison module is now an ordinary proof import; access to its private
implementation declarations is no longer needed. No original import was removed. In particular, the adopted source declaration in
`WeilConjectures.AlgebraicGeometry.EtaleStratificationLocalGluingCore` remains unchanged.

## Where the brief, the DAG or earlier work was wrong

No statement correction is needed. Constant internal module objects have two propositionally equal ring-object structures: the structure transported through the monoidal constant-sheaf functor, and the canonical sheafified ring-presheaf structure. The proof explicitly transports these structures and uses their action formulas; treating them as definitionally equal causes expensive failed elaboration. The realization comparison must also normalize the inverse used by the common encoding's scalar equivalence.

The proof keeps `B : Type` independent of `X : Scheme.{u}` throughout the private
constant-ring unit comparison. The helper's scoped instance exclusions fix only
otherwise undetermined universe parameters; all existing declarations remain unchanged.

## Second reading by J9

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
