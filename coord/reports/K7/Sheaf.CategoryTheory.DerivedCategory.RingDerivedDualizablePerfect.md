## What changed

Proved `DerivedCategory.dualizable_iff_isPerfectRingComplex` in
`Sheaf.CategoryTheory.DerivedCategory.RingDerivedDualizablePerfect`, preserving its
statement, visibility, both public imports, and independent localization universe.
All supporting lemmas are private and proved in this module. No source-library file,
public definition, target statement, or consumer was changed.

The forward implication uses compactness: the rank-one module is a compact weak
generator by the natural Hom--homology equivalence and preservation of coproducts by
homology. Duality transports compactness of the unit to the object. The existing
compact-generator telescope, compact Hom--hocolimit, and finite-stage factorization
theorems put it in the thick closure of the rank-one module. The proved perfect
triangle and summand theorems show this closure consists of perfect complexes.
`ShrinkHoms` and the existing triangulated equivalence transfer reconcile the Hom
universe with the universe of module-indexed coproducts.

The reverse implication uses the existing signed dual complex construction and
monoidal localization on bounded K-flat complexes, with explicit comparison
instances at the arbitrary localization universe. Inserting/cancelling unitors
identifies ExactPairing with precisely the identities in the statement.

Updated the item's proof, proof dependencies and proof origin in its existing DAG
node to match this argument. No new nodes or modules.
Change record: `coord/changes/K7-ring-derived-dualizable-perfect-proof-environment.md`.
The preflight-required record documents local open/universe/elaboration commands;
there is no public interface change.

## Proved and sorry left

Closed 1 of 1 holes:
`DerivedCategory.dualizable_iff_isPerfectRingComplex`
(node `lem-zl-ring-derived-dualizable-perfect`).
Added 0 holes; 0 holes remain in the item. All private helpers have complete proofs.
No decomposition or definition repair. Existing dependencies retain their own proofs
and any pre-existing transitive holes; none was introduced or moved by this delivery.

## No longer needed

Removed private imports:

- `Sheaf.Algebra.Homology.DerivedTensorSecondFactorFunctor`
- `Sheaf.Algebra.Homology.KFlatResolutionIndependentCoefficients`
- `WeilConjectures.Algebra.Homology.BoundedFlatKFlat`
- `Sheaf.Algebra.Homology.SiteDerivedTensorDescentIndependentCoefficients`
- `Sheaf.Algebra.Homology.BoundedFreeFiniteSubcomplex`
- `Sheaf.Algebra.Homology.BoundedProjectiveComplexDualPairing`
- `Sheaf.Algebra.Homology.SubcategoryLeftResolution`

The old proof dependencies below are not needed as declared inputs of this proof:

- `def-pc-tensor-complex-sheaves`
- `def-weil-abstract-derived-category`
- `lem-pc-derived-tensor-second-factor-functor`
- `lem-pc-derived-zero-third-split`
- `lem-pc-kflat-resolution`
- `lem-pc-module-bounded-flat-kflat`
- `lem-sfb-subcategory-left-resolution`
- `lem-weil-pbc-flat-tensor-exact`
- `lem-weil-pbc-hom-into-triangle-exact`
- `lem-weil-pbc-projective-module-flat`
- `lem-weil-pbc-site-derived-tensor-descent`
- `lem-zl-bounded-free-finite-subcomplex`
- `lem-zl-bounded-projective-complex-dual-pairing`

Removed the obsolete entries of the node’s top-level `tool_uses` list:
`lem-weil-pbc-site-derived-tensor-descent`, `lem-pc-module-bounded-flat-kflat`, `lem-pc-kflat-resolution`, `lem-pc-derived-tensor-second-factor-functor`, `lem-sfb-subcategory-left-resolution`, `lem-weil-pbc-hom-into-triangle-exact`, `lem-pc-derived-zero-third-split`.
The existing Hom--homology and perfect-summand approvals remain in their original order.

The finite-support coevaluation, bounded-above free resolution and finite-free
subcomplex route is replaced by the compact-generation argument. The specialized
bounded-projective pairing statement is replaced by the already proved general
signed-dual construction, and the site tensor descent statement by the existing
K-flat monoidal localization API. Consecutive-composition vanishing and split
triangles use Mathlib directly. Some underlying tensor/flatness constructions
remain transitive source-library dependencies; this is no assertion that they
can be withdrawn globally. No existing module or declaration is withdrawn.

## Where the brief, the DAG or earlier work was wrong

The original DAG plan is a valid longer strategy, but its site-level intermediary
signatures do not directly express the ordinary-module computation. The existing
compact-generation API gives a shorter complete route. The source-library theorem
`DerivedCategory.isDualizable_Q_obj` couples the localization universe to the Hom
universe, whereas this theorem intentionally does not. Its proof is adapted here
using the same proved constructions with explicit universe-generic derived-monoidal
instances, without changing that upstream declaration.

Edge cases: the rank-one generator argument uses only the implication from a
nonzero object to nonzero homology, so it is valid for the zero ring too. The
finite-sum argument includes the empty finite sum. Bounded model shifts impose no
ordering hypothesis on the chosen bounds. Neither direction assumes Noetherianity.
The unit route and all public statements are preserved.

## Second reading by K7

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
