## Worker report

The module `Sheaf.AlgebraicGeometry.AffineRelativeTorAmplitudeCriterion` states the
three assertions of `lem-trf-affine-relative-tor-amplitude-criterion`. Every theorem
has exactly `by sorry` as its proof. The canonical complex constructions have real
data. No mathematical hypothesis or source statement was corrected.

The source was read in `literature/stacks-project/perfect.tex`,
`lemma-tor-dimension-rel-affine` (Tag 0DHY), including both numbered clauses and the
whole proof. Its stalk proof also explains the inverse-image-test assertion of
the node: a skyscraper at the image point supplies any module over the base stalk.

Hypothesis and clause correspondence:

* Arbitrary commutative rings and their specified homomorphism are
  `{R A : Type u} [CommRing R] [CommRing A] (φ : R →+* A)`.
  The geometric morphism is always `Spec.map (CommRingCat.ofHom φ)`; no other
  scheme morphism or algebra structure is chosen.
* `M : CochainComplex (ModuleCat.{u} A) ℤ` is the arbitrary unbounded complex.
  `(affineModelTildeComplex (.of A)).obj M` applies the actual
  `tilde.functor (.of A)` termwise,
  with its existing zero-morphism preservation proof `tilde.map_zero`.
  Its image under `DerivedCategory.Q` is precisely the E of the node.
* The inverse-image coefficient ring is the actual
  `TopCat.Sheaf.inverseImageRing (Spec.map (CommRingCat.ofHom φ)).base
  (Spec (.of R)).sheaf`. `affineRelativeTorComplex φ M` restricts the tilde
  complex along the actual `Scheme.Modules.tensorPullbackRingMap` of that map.
  Neither absolute tensor over A nor an arbitrary ring-sheaf map is substituted.
* `a b : ℤ` and `_hab : a ≤ b` supply the prescribed interval. The antecedent
  `i < a ∨ b < i` expresses every degree outside the closed interval, including
  negative degrees.
* Clause (1) is the left side of `affine_relative_torAmplitude_iff`: every
  module sheaf F over the inverse-image ring and every such i satisfy
  `CochainComplex.sheafDerivedTensorVanishes`. This predicate requires a
  quasi-isomorphism from a K-flat resolution and zero homology of its actual
  tensor with F in degree zero. Its existential witness may depend on F and i;
  independence of K-flat resolution makes this exactly derived vanishing, with
  no extra choice assumed by the theorem.
* Clause (2) is its right side: `DerivedCategory.torAmplitudeIn
  (ModuleCat.{u} R) a b (DerivedCategory.Q.obj
  (((ModuleCat.restrictScalars φ).mapHomologicalComplex (.up ℤ)).obj M))`.
  The existing predicate quantifies over every R-module placed in degree zero,
  using the existing derived tensor and homology concentration in [a,b].
  Importing `GrothendieckAbelian.Monoidal.FlatResolution` supplies the existing
  module instances used by this predicate.
* `affine_relative_torAmplitude_inverseImage_test` repeats the identical
  all-sheaf condition and equates it to testing every base module sheaf G
  through the actual `TopCat.Sheaf.inverseImageModule ... G`. In particular
  G is not required to be quasi-coherent and the scheme map need not be
  surjective. No extra boundedness assumption is made in this assertion.
* The left side of `affine_relative_locallyFiniteTor_iff` is
  `∀ x, ∃ U, x ∈ U ∧ Scheme.HasFiniteTorDimensionOver (U.ι ≫ f)
  (DerivedCategory.Q.obj (affineTorOpenTildeComplex M U))`.
  The helper is precisely termwise open restriction, using the recorded
  `SheafOfModules.overFunctor` followed by `Scheme.Modules.overEquiv U`.
  The existing additivity theorem is installed only inside this definition;
  there is no file-local instance, hidden notation, or unbound variable.
  Restriction along the composite `U.ι ≫ f` has coefficient ring canonically
  the restriction of f-inverse-image O_V, so this is exactly the local clause.
  `HasFiniteTorDimensionOver` existentially supplies its finite interval and
  tests every module over that inverse-image ring, as the node requires.
* The right side is `∃ a b : ℤ, a ≤ b ∧ torAmplitudeIn ...`, a single finite
  R interval. All derived-category binders only specify localization models;
  none asserts finiteness or boundedness of M, the rings, or the morphism.
  There are no flatness, finite-presentation, or Noetherian hypotheses.

Dependencies and declarations read and used:

* `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and
  `Scheme.Hom`, with `Spec` and `Spec.map` from their usual affine API.
* `WeilConjectures.AlgebraicGeometry.DerivedCategory`:
  `AlgebraicGeometry.schemeDerivedCategory` and its shared module-sheaf category.
  The current source was read with `scompile.py --source`, since the older
  slopmaster2 path does not contain the upstream module.
* `Sheaf.AlgebraicGeometry.AffineQCohDerivedEquivalence`:
  `AlgebraicGeometry.exists_affineQCohDerivedEquivalence`, whose full signature
  identifies its functor with the same termwise tilde used here. We use this
  concrete complex, rather than choose an unspecified equivalence. The current
  source was also read through `--source`.
* `Sheaf.AlgebraicGeometry.AffineModelCoherentObjectComparisons`:
  `AlgebraicGeometry.affineModelTildeComplex`, whose full helper signature and
  docstring were read. A final duplication audit found this exact existing
  termwise tilde functor; the initially drafted tilde helper was removed and
  this declaration is now used directly. Its owning landed node was added
  to stmt_deps. This only reuses its canonical construction, with none of the
  extra hypotheses of that module's main theorem.
* `Sheaf.AlgebraicGeometry.FiniteTorDimensionOver`:
  `AlgebraicGeometry.Scheme.HasFiniteTorDimensionOver`, read in full locally
  and through `--source`. This is used directly on each open subscheme.
* `WeilConjectures.Topology.InverseImageModule`:
  `TopCat.Sheaf.inverseImageRing`, `inverseImageModule`, and
  `Scheme.Modules.tensorPullbackRingMap` from the existing tensor-pullback module.
  This already-landed definition node was added to stmt_deps because the
  inverse-image test appears in the statement as well as the proof.
* The new node below supplies `CochainComplex.sheafDerivedTensorVanishes`.
  It reuses the existing `CochainComplex.IsKFlat`, `SheafOfModules`,
  `SheafOfModules.monoidalCategory`, `CochainComplex.mapBifunctor`, and
  `HomologicalComplex.single`; it does not introduce another tensor product.
* The proved/stated proof inputs are imported without `public`:
  `KFlatResolutionIndependentCoefficients`, `InverseImageStructureStalkIso`,
  `RelativeInverseImageStalkRestriction`, `ModuleStalkExact`,
  `StalkKFlatTensorHomology`, `RingedModuleSkyscraper`,
  `SkyscraperComplexStalk`, and `InverseImageStalk`, in the modules named by
  their DAG records. The Mathlib tilde localization leaf is already present
  through `Mathlib.AlgebraicGeometry.Modules.Tilde`; its `tilde.toStalk` and
  localization instance were read. The algebraic localization proof dependency
  has no statement yet and therefore no module is imported for it. The
  affine quasi-compactness leaf is the existing Mathlib affine-scheme API.

Edge cases checked mathematically against both source and signatures:

* For the zero ring A, Spec A is empty and every A-module is zero. The local
  universal quantifier is empty, the sheaf tests vanish, and [0,0] witnesses
  finite R amplitude. No Nonempty/Nontrivial binder excludes this case.
* For M = 0, every fixed interval works; local finiteness follows using [0,0].
* For φ the identity map, restriction of scalars is the identity and this
  specializes to the ordinary affine criterion.
* A nonflat quotient map, a map with nonsurjective spectrum, and an unbounded
  complex all remain expressible. A complex with unbounded nonzero cohomology
  is not spuriously forced to have finite amplitude: testing with R already
  detects those cohomology groups.
* a = b and negative endpoints remain allowed. Endpoints are included, and
  tensor factors are placed in degree zero, without a cohomological sign change.

Searches for an existing statement were performed with the prescribed wrapper:

* LeanFinder: “For any commutative ring map R to A relative Tor amplitude of
  the termwise associated sheaf of an A module complex on Spec A equals Tor
  amplitude over R”. Returned derived cohomological bounds and projective
  Tor vanishing, not the relative affine comparison.
* Loogle: `DerivedCategory.torAmplitudeIn, ModuleCat.restrictScalars`.
  The service does not index the project torAmplitudeIn identifier; no match.
* Mathlib grep: `relative.*[Tt]or|[Tt]or.*relative` under AlgebraicGeometry.
  Results were unrelated relative gluing constructions.
* Source and project rg searches of relative Tor names, HasFiniteTorDimensionOver,
  and the item id found no existing theorem. The project absolute
  `affine_torAmplitude_iff` was read: it tensors over A and cannot replace
  relative amplitude over R. The existing finite-relative-Tor results impose
  perfectness and/or hypotheses on the map and therefore are not this item.
* For the new predicate, LeanSearch, LeanFinder and Mathlib grep were repeated
  with the queries recorded verbatim, and their raw result summaries retained
  in the new node. Direct rg of WeilConjectures and lean/Sheaf and the blueprint
  search found only the scheme-structure-sheaf predicates described below.

The theorem docstrings retain all six steps of the DAG proof across the three
assertions: stalk and scalar identifications; K-flat tensor stalks and skyscraper
recovery; prime-local algebraic detection; inverse-image skyscraper tests; finite
subcover uniformization; and the converse using the whole affine neighbourhood.
No statement is disputed and no statement_change is needed.

Validation: both delivered modules are checked individually, in dependency order,
by the required scompile.py wrapper. Earlier diagnostics were an incorrectly
spelled proof-import module, a parenthesis/method parsing error, missing existing
module-category instances, and additivity for open restriction; each was repaired
using the recorded modules and canonical constructions. A long line was wrapped.
The final compilation and delivery preflight results are recorded below.

## New nodes

`def-trf-ringed-complex-derived-tensor-vanishing` defines derived tensor vanishing
of an arbitrary complex with a module in degree zero on a general ringed site,
using actual K-flat resolutions and total tensor cohomology. Source: Stacks
06YS/06YU, specialized as required in 0DHY. The existing DAG node
`def-pc-derived-tensor-cohomology-vanishes` and its complex variant both require
the structure sheaf of a scheme. They cannot be applied to f-inverse-image O_V,
which is generally not the structure sheaf of a scheme. No general ringed-site
predicate was found by the recorded LeanSearch, LeanFinder, Mathlib grep,
project/upstream rg and blueprint searches. This new definition reuses all the
underlying sheaf-module, K-flatness and tensor notions. Its module contains one
actual Prop-valued definition and no postponed theorem. The item cites the new
node directly; its ancestry retains lem-trf-local-term-locality and the item's
full existing via chain. No dependency module or dependency repair is delivered.

Final self-check: the first delivery dry run passed preflight and compiled both
modules (`47e538b5d6`, not pushed). The final duplication audit then replaced
our termwise tilde helper by the already landed `affineModelTildeComplex`;
we recompile and run the dry run again for this final form before pushing.

The final version, reusing the existing termwise tilde functor, compiled cleanly
in both sandbox and library positions through scompile.py; no warnings were
emitted. The item changes only lean and adds the new definition and two landed
statement dependencies. Both primary Lean record signatures were checked
verbatim against their files. There are exactly three named sorry theorems,
all belonging to the item, and no sorry in any definition. No delivered line
exceeds 100 characters. The reused tilde helper has no dependency path back
to the item. The required final dry run and delivery run follow this check.

## Second reading by Q102

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
