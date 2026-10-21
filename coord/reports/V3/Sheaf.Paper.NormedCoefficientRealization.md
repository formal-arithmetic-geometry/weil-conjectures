## What changed

Proved `AlgebraicGeometry.ProEtale.NormedCoefficientRealization.normed_coefficient_realization`
in `Sheaf.Paper.NormedCoefficientRealization`, with its statement and all public definitions
unchanged. All added helpers are private and proved.

Constructed the finite intermediate field as the image of `IsAlgClosed.lift`, transported
finite dimension through `equivFieldRange`, and proved the embedding isometric by uniqueness
of the spectral absolute value. The membership clause of `extension_integers_dvr` identifies
the existing chosen integer subrings with norm unit balls. `RingEquiv.restrict` constructs the
integer equivalence. Postcomposition and inverse postcomposition construct the actual
condensed ring isomorphisms, and their inclusion square is checked sectionwise.

For every coefficient isomorphism, exact scalar restriction gives the derived equivalence,
triangulatedness and bounds. The existing `constructible_comap` and `constructible_of_iso`
helpers, together with the homology comparison, prove bounded constructibility in both
directions. Derived extension is compared using its canonical exact-functor comparison.
The direct-image isomorphism is the right mate of the specified inverse pullback comparison
under the actual derived adjunctions. The existing mate invertibility lemma applies because
the vertical functors are equivalences. `mateEquiv_counit` and cancellation prove precisely
the required counit equation.

Added proof-only imports of `Sheaf.CategoryTheory.MateIsoAlongEquivalences` and
`Sheaf.AlgebraicGeometry.ProEtaleModuleConstructiblePullback`. Updated the item's proof,
proof dependencies and origin to this route. No other module, signature, definition,
visibility or public import is changed. No consumer adaptations or change record are needed.
The unit's direct-image finiteness route remains unchanged.

## Proved and sorry left

Closed 1 of 1 original holes:
`AlgebraicGeometry.ProEtale.NormedCoefficientRealization.normed_coefficient_realization`
(node `lem-sfb-normed-coefficient-realization`). Added 0 holes, split off 0 statements.
The final single-file server compile passed without diagnostics in 18.0 seconds.
There are no remaining `sorry` tokens in the delivered module. Existing dependencies are
used with their published proofs; this is a proof from the existing library, not a claim
that all transitive library holes are closed.

Edge cases: the proof uses no positive extension-degree or nonzero-module hypotheses;
E = Q_ell, ell = 2, empty schemes, zero derived objects and identity scheme morphisms
are covered. Scalar restriction is treated for arbitrary coefficient isomorphisms.

## No longer needed

Removed these unused proof-only imports:

- `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`
- `Mathlib.Algebra.Homology.ShortComplex.PreservesHomology`
- `Mathlib.Algebra.Homology.DerivedCategory.KInjective`
- `Mathlib.CategoryTheory.Localization.Predicate`
- `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`
- `Sheaf.Paper.CartesianCoefficients`
- `Sheaf.SixFunctors.ResolvingDerivedAdjunction`

The published exact-functor API is already publicly reachable through the required scalar
and derived-pushpull modules. No extra proof import is needed for that API. The categorical
mate argument replaces the K-injective construction, the separate pointwise transpose
normalization, and the use of Cartesian-coefficient exactness in the original plan.
Removed from this node's proof dependencies:

- `def-sfb-constructible-module`
- `def-sfb-finitely-presented-module`
- `def-sfb-locally-finitely-presented`
- `sk-def-sfb-coefficient-morphisms`
- `lem-sfb-comap-preserves-k-injectives`
- `sk-def-sfb-derived-categories`
- `lem-sc-kinjective-quasi-iso-comparison`
- `sk-prop-sfb-cartesian-coefficients`
- `lem-sfb-resolving-derived-adjunction-normalization`
- `lem-weil-pbc-localization-universal-property`

The finite-presentation and local-finite-presentation steps are reused through the proved
constructibility helper instead of being rebuilt here. Definitions still needed for the
statement remain in stmt_deps or are dependencies of the retained helpers; none is withdrawn.
The old tool approvals for `lem-sfb-comap-preserves-k-injectives` and
`lem-sfb-resolving-derived-adjunction-normalization` are removed as unused.
No module is withdrawn, and this report makes no whole-library unreachability claim.

## Where the brief, the DAG or earlier work was wrong

The ten-step DAG plan was valid but longer than necessary. The existing theorem
`isIso_mateEquiv_of_isEquivalence_of_fullyFaithful` supplies invertibility of the exact
mate required by the statement, so there is no need to construct a direct-image comparison
on K-injective representatives and then separately normalize it. All public statements
remain unchanged. No new nodes and no statement disputes.

Searches through the prescribed msearch service: LeanFinder for finite p-adic normed-field
embeddings returned the standard PadicAlgCl norm-extension facts, Loogle confirmed
`spectralNorm_unique_field_norm_ext`, and source grep located its declaration. Project
source searches found the scalar equivalence, constructibility helpers and mate lemma used
above. No theorem already states the whole realization result.

## Second reading by V3

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
