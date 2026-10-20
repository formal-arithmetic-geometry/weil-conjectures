## What changed

Proved the thirteen existing theorem holes in
`Sheaf.AlgebraicGeometry.NormalizedSupportTriangle`. All existing public signatures,
public imports, and non-theorem bodies are preserved. Some declarations are reordered
so that open restriction and its derived comparison specialize the general transport
construction rather than duplicate it.

The ordinary maps come from the universal property of the supported-sections kernels.
Terminal-object uniqueness and the inverse-image adjunction identify their components
with actual restriction maps. For an injective sheaf, a section supported on B inside
U = T minus C glues to zero on W = T minus B. Restriction of an injective sheaf to
U union W is surjective, so the glued section lifts to T. Sheaf uniqueness identifies
the kernel with the intersection support. This proves short exactness degreewise.

Added two general, proved theorem modules: `Sheaf.CategoryTheory.UnboundedInjectiveModel`
and `Sheaf.CategoryTheory.UnboundedDerivedBoundary`. The first constructs termwise
injective K-injective models using the source weak factorization system and the
existing functorial injective complex embedding theorem. The second uses the source
boundary formulas and their naturality to construct and uniquely normalize the
unbounded derived boundary. The main module applies this theorem to the support
sequence. The bounded-below injective model then identifies the resulting triangle
with the canonical triangle of the short exact complex.

The transport comparison uses the right-derived universal property and preservation of
K-injectives by etale inverse image. For a scheme isomorphism, both global and
complementary section maps are isomorphisms, so their kernel map is an isomorphism.
Updated the existing DAG proof and added nodes for the two general lemmas.
In the short-exactness proof, the supported-section functor, its inclusion, and inverse
image are locally irreducible; their proved APIs avoid repeated expansion of kernel
and sheafification constructions. No global reducibility attribute is changed.

## Proved and sorry left

Closed 13 of 13 original holes, by declaration name in `AlgebraicGeometry.Etale`:

- `supportIntersection_closed`
- `supportOnOpen_closed`
- `exists_unique_supportInclusion`
- `exists_unique_supportOpenRestriction`
- `supportInclusion_restriction_zero`
- `supportLocalizationComplex_shortExact`
- `exists_unique_supportLocalizationBoundary`
- `exists_unique_supportOpenDerivedComparison`
- `normalizedSupportTriangle_distinguished`
- `supportOnOpen_complement`
- `exists_unique_supportTransport`
- `exists_unique_supportTransportComparison`
- `derivedSupportTransport_isIso`

Also proved `DerivedCategory.nonempty_injectiveModel` and
`CategoryTheory.ShortComplex.exists_unique_unboundedDerivedBoundary` in the two new
modules. Holes added: zero. Holes remaining in all three delivered modules: zero.
No unfinished statement was split off. These proofs use existing stated dependencies,
including `CochainComplex.exists_functorial_injective_complex_embedding`, whose
remaining proof is an existing separate item.

## No longer needed

The following former direct proof dependencies are not needed:

- `lem-weil-pbc-open-closed-short-exact`: direct sheaf gluing and injective restriction
  replace open-closed recollement.
- `def-sp-injective-resolutions`: the proved source bounded-below injective model is
  used directly.
- `lem-weil-pbc-module-sheaves-enough-injectives`: the main category is
  `Sheaf T.smallEtaleTopology (ModuleCat A)`. The generic source Grothendieck-sheaf
  instance already supplies its enough injectives; the separate theorem about
  `SheafOfModules` is not used.
- `def-weil-sheaf-of-modules-category`: no ringed-site alias is needed for these
  constant-coefficient sheaves; the existing `CategoryTheory.Sheaf` category suffices.
- `lem-weil-pbc-extension-by-zero-adjunction`: the general etale extension-by-zero
  adjunction and exactness from `lem-weil-pbc-etale-restriction-injectives` already
  supply the needed preservation of K-injectives.

Removed the obsolete top-level `tool_uses` entry for
`lem-weil-pbc-module-sheaves-enough-injectives`; the inverse-image-exactness approval
is retained.

The direct edge to `lem-weil-pbc-kinjective-hom-derived` moves to the new unbounded
boundary node; this remains a transitive dependency. No unit statement or realized
unit step is bypassed, and no module is withdrawn. This is local pruning, not a claim
that these nodes have no other consumers.

Discarded candidate private imports after compilation:
`WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme`,
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExact`
(already public through the new boundary module),
`Sheaf.AlgebraicGeometry.EtaleModuleEnoughInjectives`,
`Sheaf.CategoryTheory.RingedSiteModules`, and
`WeilConjectures.SixFunctors.OpenClosed.Exact`.

All original public imports remain, including `SupportRestrictionTriangle`, to preserve
the public interface. The new proof does not depend on that module's non-normalized
support triangle: the ordinary arrows are constructed directly from kernels and the
boundary is fixed by its injective-complex normalization.

## Where the brief, the DAG or earlier work was wrong

The stated boundary is natural on the entire unbounded derived category, although
only its distinguishedness is requested for bounded-below objects. The source library
provides the required unbounded model-level boundary and naturality, but packages its
final natural transformation only for bounded-below objects. The two new proved lemmas
supply the missing general interface without altering the statement.

Preflight requires LeanSearch, Loogle/LeanFinder, and source grep as three distinct
search kinds. LeanFinder plus Loogle counts as one kind; explicit LeanSearch queries
and results have been added to both new nodes.

The generic Mayer-Vietoris sheaf-condition interface fixes universes that do not match
these module sheaves. The proof uses the same two-open square and derives its section
pullback directly from the sheaf amalgamation axiom, allowing the required universes.

## New nodes

`lem-pur-unbounded-injective-model` is realized by
`Sheaf.CategoryTheory.UnboundedInjectiveModel`. It factors a complex-to-zero map by the
monomorphic quasi-isomorphism weak factorization system, then uses its lifting property
to exhibit every term as a retract of an injective object supplied by the existing
functorial embedding. It is proved, with no new hole.

`lem-pur-unbounded-derived-boundary` is realized by
`Sheaf.CategoryTheory.UnboundedDerivedBoundary`. It combines the canonical short exact
complex boundary, the source model-level naturality formula, and termwise injective
K-injective models to obtain the unique normalized boundary. It is proved, with no new
hole. The original node retains the blueprint's two-open gluing and injective-complex
triangle route. Both new nodes record the exact step-6 provenance under
`lem-pur-support-restriction-triangle`. Whole-blueprint searches for K-injective models,
injective terms, and connecting natural transformations found no duplicate of these
two general unbounded interfaces; the existing injective-terms support triangle is
bounded below.

Validation: `lcompile.py --all` compiled all three delivered modules with no errors
or warnings; the final main module with local instance registrations took 47.0 seconds. A textual comparison also confirmed
all original signatures and non-theorem bodies are unchanged.

Change record: `coord/changes/G6-normalized-support-proof-scopes.md` documents the
proof-local attributes requested by the visibility scan and audits all current
consumers. Existing public statements, definitions, and public imports are unchanged;
no consumer requires adaptation. The three private instance proofs are registered only
locally in this file.

## Second reading by G6

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
