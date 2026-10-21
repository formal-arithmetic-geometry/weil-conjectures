## What changed

Filled `DerivedCategory.field_complex_cohomology_splitting` in
`Sheaf.Algebra.Homology.FieldComplexCohomologySplitting`, keeping its complete signature,
universes, public imports and original source docstring. All added helpers are private and proved; all three helper instances are local.
Only this Lean module and its existing node are changed.

The proof uses the existing proved
`CochainComplex.nonempty_nullHomotopy_of_homologyMap_zero` in
`WeilConjectures.CategoryTheory.SplitCategoryNullHomotopy`. Vector spaces are projective and
injective, so it proves both homotopy uniqueness and K-projectivity for every field complex.
Mathlib's `CochainComplex.IsKProjective.quasiIso_iff` and `Qh_map_bijective` then supply the
quasi-isomorphism and localization steps. Arbitrary cohomology maps lift by sections of the
cohomology quotients and extensions from cycles. Canonical factorization isomorphisms identify
the resulting Hom bijection with exactly the map in the statement.

For the normalization clause, the prescribed complements give a projection onto V along
B+T. The cohomology quotient restricted to V is bijective: injectivity uses exactness and
B∩V=0, and surjectivity uses Z=B+V. Its inverse gives the inclusion of representatives;
the projection gives the map back. These maps have the prescribed range, kernel and value
on cycles. Their composites are identity and homotopic to identity, respectively.

The zero-differential models are explicit constructions with the given cohomology spaces.
Finite support supplies bounds (also when support is empty), and finite dimension supplies
finite projective terms. Image/kernel subspaces of the degreewise idempotents are also
explicit. Lift their inclusion/projection maps using the Hom bijection, then prove all
splitting identities, the binary biproduct isomorphism, the commuting block formula, and
comparison of arbitrary splittings by category identities.

Private proof imports added: the split-category null-homotopy module,
`Mathlib.Algebra.Homology.DerivedCategory.KProjective`,
`Mathlib.Algebra.Category.ModuleCat.Projective`,
`Mathlib.Algebra.Category.ModuleCat.Injective`,
`Mathlib.RingTheory.SimpleModule.InjectiveProjective`, and
`Mathlib.Algebra.Homology.ShortComplex.ModuleCat`.

The node's proof, proof_deps and proof_origin now describe this argument. It adds the existing
proved null-homotopy tool and retains the original mathematical prerequisites. No public API,
definition used by a target, source-library declaration, or downstream module changes. No new
`open` command or global instance is introduced.

## Proved and sorry left

Closed: `DerivedCategory.field_complex_cohomology_splitting`
(node `lem-trf-field-complex-cohomology-splitting`), the module's single original hole.
All five conjunction clauses, including every normalization and retract equation, are proved.
Holes closed: 1. Holes added: 0. Holes left in the delivered module: 0.
No statements are split off. No new axioms or unproved helper statements are introduced.

## No longer needed

Removed redundant private proof imports `Mathlib.Algebra.Module.Projective`,
`Mathlib.LinearAlgebra.FiniteDimensional.Defs`, and `Mathlib.RingTheory.Finiteness.Defs`;
the projectivity import is provided by the category-level projectivity API and the finiteness
notions already occur in the retained public interface imports. All original public imports
remain verbatim. `Mathlib.LinearAlgebra.Basis.VectorSpace` is retained for complements.

No existing DAG dependency, module or unit step is withdrawn. The manually constructed
inverse-localization functor in the old plan is replaced by Mathlib's K-projective Hom
bijection; the general null-homotopy argument is reused from its already proved module.
There is no reason to prove a duplicate field contraction or localization equivalence.
No declaration is removed from the adopted source library.

## Where the brief, the DAG or earlier work was wrong

The statement is unchanged and all its clauses are valid, including unbounded and
infinite-dimensional complexes, the zero complex, empty finite support, and idempotents
0 and 1. No mathematical repair was required. The earlier search did not reuse the existing
proved abstract split-category null-homotopy lemma; that lemma shortens the planned
homotopy and localization steps considerably. It is used only as a proved general tool
below the unit level, preserving the trace-transport unit route.

Several intermediate compile requests returned exit 124 with “no answer from the compile
server”; these were retried under the brief's busy-server rule, without changing the
launcher scripts or compile timeout.

Validation: the complete module compiled through `lcompile.py` in 4.9 seconds with
exit code 0, no warnings, and no remaining `sorry`. A source comparison confirms that the
original theorem signature, docstring and public imports are preserved verbatim; every
new helper is private and every line is at most 100 characters. `import_direction.py may`
confirmed that the reused null-homotopy import introduces no cycle. The delivery tool
performs the independent axiom probe and server preflight before pushing.

## Second reading by K6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
