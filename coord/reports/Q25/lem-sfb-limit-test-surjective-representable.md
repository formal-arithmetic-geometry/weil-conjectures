## Worker report

States `CategoryTheory.surjective_of_affine_locallyOfFinitePresentation_tests` in
`Sheaf.AlgebraicGeometry.LimitTestSurjectiveRepresentable`. The only theorem has
proof `sorry`; there are no new definitions or auxiliary proof obligations.
The source read is Stacks `criteria.tex`, Tag 07WI,
`lemma-check-property-limit-preserving`, statement and proof, specialized to
surjectivity. The seven-step proof docstring follows the node's accepted split.

Clause-by-clause correspondence:

- The arbitrary base is `{S : Scheme.{u}}`; no Noetherian, compactness or separation
  hypothesis is imposed. Explicit universes `u v₁ w₁ v₂ w₂` implement the size
  convention, permitting distinct sizes for the two total categories.
- Categories over S-schemes are `F` and `G : BasedCategory (Over S)`, with the
  separate `IsFibredInGroupoids F` and `IsFibredInGroupoids G` hypotheses.
  Their morphism is the based functor `f : BasedFunctor F G`.
- `hf : IsRepresentableByAlgebraicSpaces f` supplies an algebraic-space
  presentation of every scheme 2-base change. `HasSpaceBaseChange f T t Z p`
  compares the actual triple category with the discrete fibred groupoid of `Z`,
  by an equivalence over the base and a specified 2-isomorphism on the projection.
  Thus `p` is the projection of the representing space, not an arbitrary map.
- An object `y` over `T` is rendered by
  `t : BasedFunctor (discreteModuli (yoneda.obj T)) G`. The fibred Yoneda
  equivalence identifies these with fibre objects, retaining their isomorphisms.
  This imposes no extra condition on y: all arrows of a fibred groupoid are
  cartesian, so any based functor preserves the required cartesian arrows.
- `hLimits : FibredGroupoidLimit.ObjectsDescend G` is precisely descent of
  objects, up to fibre isomorphism, along small directed affine inverse limits.
  Its definition quantifies over nonempty directed preorders `I : Type u`,
  affine stages and an affine limit cone over S. The lift it requests is
  cartesian because G is fibred in groupoids. Neither `ArrowsDescend` nor
  `ArrowEqualitiesDescend`, nor limit preservation of F, is assumed.
- `hTests` restricts T by `IsAffine T.left` and
  `LocallyOfFinitePresentation T.hom`. It asserts point surjectivity for every
  presentation `Z,p` with `HasSpaceBaseChange f T t Z p`.
- `AlgebraicSpace.IsJointlySurjective (fun _ : Unit ↦ p)` renders the node's
  single-map surjectivity on field-valued point classes. Its definition asks
  that every K-valued target point lift to Z after a field extension K → L.
  This is exactly equality of the image point class with the original class.
- The conclusion has the same `T,t,Z,p` and actual base-change condition, with
  no affineness or finite-presentation restriction. Quantifying over all
  presentations merely makes the node's presentation-independent assertion
  explicit; equivalences over T identify these presentations and projections.

Recorded dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, `Scheme.Hom`.
- `def-weil-size-convention` is metatheoretic; it has no object to import.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicSpace`, its
  `IsAlgebraicSpace` and scheme-test predicates, with their full signatures.
- `Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation`:
  `AlgebraicGeometry.LocallyOfFinitePresentation`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `fibreProduct_isAlgebraicSpace`, `etaleCover_pullback`,
  `etale_fibreProduct_isScheme`; the module is imported publicly for the
  statement's recorded point convention and the proof's pullback step.
- Added the already-landed `def-sfb-stable-pointed-moduli-groupoids` to
  statement dependencies: its module `StablePointedModuliGroupoids` supplies
  `IsFibredInGroupoids`, `discreteModuli`, `moduliTwoFiberProduct`,
  `HasSpaceBaseChange` and `IsRepresentableByAlgebraicSpaces`. No moduli-curve
  hypothesis is used from this multipurpose module.
- Added the already-landed `def-sfb-fibred-groupoid-limit-preserving`:
  `Sheaf.AlgebraicGeometry.FibredGroupoidLimitPreserving` supplies precisely
  its `ObjectsDescend` component, with `Object` and `Lift`.
- Added the already-landed `def-trf-algebraic-space-jointly-surjective-family`:
  `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity` supplies
  `AlgebraicSpace.IsJointlySurjective` (also publicly imported by the recorded
  fibre-product module).
- Plain proof imports cover `IsOpenImmersion`, `Limits.colimit`/`IsColimit`,
  `Scheme.isBasis_affineOpens`, `Spec.reflective`, and affine scheme maps,
  matching all the node's recorded proof dependencies. There is no import of
  the downstream Artin representable-diagonal criterion.

Edge cases checked before writing: the empty test scheme has no field-valued
points, so both test and conclusion predicates are vacuous there; empty S
causes no restriction. Directed systems are nonempty and indexed in the scheme
universe, including a singleton system and stages with the zero ring. S may
be non-quasi-separated and non-quasi-compact: the affine-open reduction is
pointwise and needs no finite cover or affine intersections. No stack descent
condition and no fully faithful limit comparison have been inserted. A scheme
presentation is a special case of the same algebraic-space condition.

Searches actually run:

- `msearch.py leanfinder`: “A representable morphism of categories fibred in
  groupoids is surjective if it is surjective on affine schemes locally of
  finite presentation and the target is limit preserving on objects”. Eight
  results: scheme joint-surjectivity permanence, Zariski local representability,
  scheme surjectivity, and related facts; none is this fibred-groupoid test.
- `msearch.py loogle`: `CategoryTheory.Functor.IsFiberedInGroupoids,
  AlgebraicGeometry.Scheme, Function.Surjective`. Zero hits; Loogle reported
  the first guessed identifier unknown. This is not evidence against the
  correctly named project predicate, which was located by local searches.
- `msearch.py grep`, Mathlib AlgebraicGeometry:
  `IsLimitPreservingOnObjects|surjective.*[Ll]imit|[Ll]imit.*surjective`.
  Six hits in PullbackCarrier, AffineTransitionLimit, Gluing and UnderlyingMap;
  none states this result.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and the upstream name map,
  by the node id, `limit.*surjective`, `surjective.*limit`, and the chosen
  theorem name found no existing declaration. The Artin criterion docstring
  refers to this node as a prerequisite but does not state the test.
- `rg` by `Fibred`, `LimitPreserving`, `IsRepresentableByAlgebraicSpaces`,
  and the definition names in the DAG and project sources located the landed
  reusable interfaces above. Their complete relevant signatures and docstrings
  were read before use. No missing notion or unusable dependency remains.

The item statement, proof and proof dependencies are unchanged. Only its Lean
record and the three added, landed definition dependencies are delivered.
No statement dispute or source correction was needed.

Validation: `scompile.py Q25 lem-sfb-limit-test-surjective-representable` compiled
this file both as a sandbox and under its library module name on the server,
without errors or warnings. All variables are explicitly bound and
`autoImplicit` is disabled. The required delivery dry run follows.

## Second reading by Q25

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
