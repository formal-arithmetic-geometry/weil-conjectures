## What changed

The definition and API change record, including the exact old and new interfaces, is
`coord/changes/supported-hom-normalized-model-api.md`.

Proved `supportedKummerSupportHomNaturality` by constructing the normalized cone models and
the actual pullback comparison. The resolution comparison is a lift against the pulled-back
mono quasi-isomorphism, so it extends the resolution unit required by the statement.
The closed exchange is invertible by finite base change. Its compatibility with the constant
unit gives the square for evaluation at one. The two specified cone projections then give
the cone square; localization and homology give the required pullback identity. The first
cone projection gives the forgetting-support identity.

The normalized short exact sequence is proved with its evaluation formula, rather than
choosing an unspecified isomorphism from the existential sequence statement. Public model
definitions use generic categorical records and fixed complex functors to avoid expanding
functorial-resolution choices during elaboration. The data and normalizations are preserved.
The node proof and its dependencies follow this argument. The existing proved cone and
rank-one-section helpers in `ClosedSupportHom` and `ClosedSupportHomSequence` are exposed as
public APIs, so the item can import them without loading the entire private environments.
The standard resolution is packaged together with its proved K-injectivity, mono
quasi-isomorphism unit and lifting property. This package fixes the existing construction;
it does not choose a new resolution. Evaluation normalization is recorded as equality
with the canonical chain map, with a proved equivalence to the original elementwise
evaluation formula. Both additional modules were unclaimed when inspected. Their existing public theorem
signatures are unchanged. The original short-exact-sequence theorem now follows from the
new canonical-map version, using the same proof of exactness.

The site properties are named once, and the canonical abelian structure exposes pointwise
addition on morphisms; `closedSupportEtaleAbelian_eq` proves that this is the original
structure. The linear structure is likewise named, with a reflexivity proof
`closedSupportEtaleLinear_eq` of equality with the original structure. These local
instance choices avoid repeating sheafification and inherited
preadditive constructions in terms. The private generic cone constructor uses the canonical
map directly, so normalization is reflexivity before specialization. Named proof accessors
provide zero-composite and exactness proofs without a native existential elimination.
The evaluation-square condition is also formed at the generic record before specialization.

The shared Hom source is explicitly the direct image of the rank-one constant sheaf.
`closedSupportHomSource_eq` records its original formula. Restriction is the named natural
transformation `closedSupportSectionsPullback`, also used in `closedSupportHom` itself;
its component theorem records the original global-section pullback map. The normalized
chain-map condition is a family on arbitrary complexes, and a generic lemma specializes
compatibility to the fixed resolutions. Thus the mathematical normalization is unchanged.
`ClosedSupportHomSequence` is a public dependency of `ClosedSupportHom`, because its named
canonical sheaf structures occur in the latter's public APIs.

The generic diagram takes the canonical natural transformation and derives the chain-map
equality predicate from it. This makes the diagram and its constructor use the same
expression, rather than comparing two expanded normalization predicates at each site.


The Hom-map family has an explicit type using the public complex functors. This checks
its conversion once at the definition, instead of repeating a large inferred-type
comparison in each specification and record construction. The component formula uses
categorical associativity explicitly.

Validation: all three delivered modules compile; the assigned module takes 35.2 seconds.
The assigned theorem and both original supporting theorems have only `propext`,
`Classical.choice` and `Quot.sound` as axioms. The current original consumer
`OrdinarySupportedCartierKummer` compiles unchanged against the new APIs.

The four quarantined original consumers (`CartierKummerMap`,
`CompactProductProperSupportCompatibility`, `SupportedCupFunctoriality`, and
`SupportedHomPullback`) also compile unchanged against the new APIs. All five consumer
sources were verified identical to the current repository or quarantine originals, then
removed from the sandbox; no consumer adaptation is delivered.

## Proved and sorry left

Closed: `AlgebraicGeometry.Etale.supportedKummerSupportHomNaturality` (one original hole).
Added: none. Remaining in the delivered module: none. This is a proof, not a decomposition.

## No longer needed

No module is withdrawn. The unused specialized `supportedHomModelMap` wrapper is
removed: the generic model record uses `Functor.supportedHomResolutionMap` directly,
with the same derived resolution-unit formula. No external declaration uses the old
wrapper; the model-isomorphism normalization is preserved. The proof does not directly use the former stalkwise exchange route
(`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk`,
`WeilConjectures.SixFunctors.OpenClosed.Stalk`, and
`WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint`): finite base change already proves
the required closed exchange. These modules may still occur transitively in the library.
The former direct imports of `Sheaf.CategoryTheory.KInjectiveTotalDerived` and
`WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp` are unnecessary:
the existing K-injective resolution computation supplies the model isomorphism directly.
Other removed direct imports are
`WeilConjectures.SixFunctors.OpenClosed.Exact`,
`WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact`,
`WeilConjectures.AlgebraicGeometry.EtaleModuleSheavesGrothendieckAbelian`,
`WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolutionInjective`,
`Mathlib.CategoryTheory.Preadditive.Injective.Basic`,
`WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs`, and
`WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs`: their required declarations are
already available through the retained public interfaces.
The extension-by-zero adjunction is used through the normalized short-exact-sequence proof;
no independent preservation-of-K-injectives argument is needed.

The former route also no longer uses these direct planned nodes; their obsolete `tool_uses`
entries were removed, preserving the remaining approvals in order:

- `lem-weil-pbc-closed-immersion-base-change`
- `lemma-openclosed-stalk-upperstar`
- `lemma-weil-pbc-geometric-stalk-conservative`
- `lem-weil-pbc-extension-by-zero-exact`
- `lem-weil-pbc-right-adjoint-preserves-kinjective`
- `lem-weil-pbc-kinjective-total-derived`
- `lem-weil-pbc-kinjective-hom-derived`

## Where the brief, the DAG or earlier work was wrong

Resolving the pulled-back resolution alone does not construct a comparison into the already
specified functorial resolution of the pulled-back original complex. The proof uses the
lifting property against its map to zero instead. The public existential short exact
sequence statement does not specify evaluation at one, so its proof now exposes the
canonical map and its exactness. The item uses that normalized version directly.
The Hom functor is shared with the canonical sequence, so the normalization does not
recompare two expanded functor constructions. The cone model is kept generic to prevent
the kernel from repeatedly unfolding the sheaf and functorial-factorization constructions.

## Second reading by E1

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
