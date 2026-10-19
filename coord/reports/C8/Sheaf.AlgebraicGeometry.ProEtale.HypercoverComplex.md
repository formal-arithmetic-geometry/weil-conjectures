## What changed

Proved both holes of `Sheaf.AlgebraicGeometry.ProEtale.HypercoverComplex`:
`hypercoverAbelianRows_additive` and `hypercover_complex_natural_iso`, retaining
all existing public signatures and constructions.

The proof constructs the restriction augmentation into the actual alternating
section total. Weak contractibility gives exact section evaluation; the existing
bounded-below column comparison gives invariance under quasi-isomorphisms.
Matching-cover local lifting and injective hypercover exactness give the
injective-row comparison. The existing bounded-below row augmentation theorem
then identifies injective total sections with evaluation. Mathlib supplies
bounded-below injective resolutions. The derived unit and K-injective resolution
comparison maps assemble a natural isomorphism, with homotopies identified by
the existing generic bounded-below cylinder helper. No comparison object is
introduced by a new existential definition.

Generalized the ring universe in the already proved theorem
`CategoryTheory.ringedHypercover_injective_augmentation_exact_ring` of
`Sheaf.CategoryTheory.RingedHypercoverInjectiveAugmentationRing`. Its explicit
free-module construction already supports this generality; only the theorem's
ring binder and two corresponding proof annotations change. The module is
unclaimed. The change record is
`coord/changes/C8-hypercover-ring-universe.md`; its users table covers both old
callers and the new item caller. The two old caller files are unchanged and compiled against the generalized
theorem (5.0 s and 4.8 s); the revised item compiled in 24.2 s. Temporary
unchanged consumer copies were removed after these checks. The attachment of
`lem-sc-ringed-hypercover-injective-augmentation-ring` records the new Lean type;
the mathematical statement is unchanged.

Updated `det-pe-hypercover-complex` to record the actual generic resolution and
cylinder route. All added proof imports are private imports; no new module,
public helper, target signature change, or definition change is delivered.

## Proved and sorry left

Closed two of two item holes:

- `AlgebraicGeometry.Scheme.ProEt.hypercoverAbelianRows_additive`.
- `AlgebraicGeometry.Scheme.ProEt.hypercover_complex_natural_iso`.

No `sorry` remains in the item module. No holes were added or split off.
The adapted dependency
`CategoryTheory.ringedHypercover_injective_augmentation_exact_ring` had zero
holes before and has zero holes after its universe generalization. The proof
uses the stated comparison lemmas, whose own proof status is independent of
this delivery.

Edge cases follow from the constructions: negative simplicial columns are
zero; a common lower bound is the minimum of the two term bounds; empty total
diagonals are zero; the degree-zero row comparison uses both augmentation
injectivity and exactness; and naturality permits different bounds on its two
coefficient complexes. Covers are used only for injective-row descent, while
weak contractibility is used only for exact column evaluation.

## No longer needed

Removed the proof import
`Sheaf.Algebra.Homology.BoundedBelowInjectiveResolution` and the direct proof
dependency/tool-use entry `lem-sc-bounded-below-injective-resolution`.
Its declaration is restricted to commutative coefficients in a common universe;
Mathlib's generic `CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective`
provides exactly the bounded-below replacement required here, after the existing
Grothendieck theorem supplies enough injectives. This is pruning of the wrapper,
not of the unit's bounded-below injective-resolution step.

No other declared dependency is pruned. The commutative comparison theorem of
`Sheaf.AlgebraicGeometry.ProEtaleHypercoverComputesBoundedComplex` is not applied;
only its already proved generic `map_eq_of_boundedBelow_homotopy` helper is used.
The unit's existence and hypercover-descent route is retained.

## Where the brief, the DAG or earlier work was wrong

The original resolution wrapper does not allow the arbitrary ring sheaves and
independent universes of this item; the generic Mathlib construction does.
The ringed hypercover exactness theorem had the unnecessary public restriction
`RingCat.{max u r}`, although its internal construction works with `RingCat.{r}`.
The recorded universe generalization repairs this mismatch without changing
any geometric, matching, injectivity, or coefficient hypothesis.

The retained earlier report omitted that dependency adaptation and described
all imports as necessary. This delivery records the change and prunes the
unused wrapper. No new mathematical statement or new node is needed.

## Second reading by C8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
