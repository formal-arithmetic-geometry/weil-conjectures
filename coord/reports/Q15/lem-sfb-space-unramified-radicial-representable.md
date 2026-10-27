## Worker report

The module `Sheaf.AlgebraicGeometry.SpaceUnramifiedRadicialRepresentable` states
`AlgebraicGeometry.AlgebraicSpace.isRepresentable_of_unramified_universallyInjective`.
Its only proof is `sorry`; it introduces no definitions. The node is unchanged except for
its `lean` record. No statement correction or disputed statement is needed.

Source read: `literature/stacks-project/spaces-more-morphisms.tex`, Tag 05W6,
`lemma-universally-injective-unramified`, including all four equivalent conditions,
the moreover assertion, and its proof. This node requests just representability under
condition (2); the Lean conclusion does not assert the other moreover properties.

Clause-by-clause correspondence:

- The arbitrary base scheme is `{S : Scheme.{u}}`, with explicit `universe u`.
  The size convention is metatheoretic and requires no additional object or hypothesis.
- The two algebraic spaces over that base are `{X Y : AlgebraicSpace S}`. This is the
  existing full subcategory of big-fppf sheaves having representable diagonal and a
  representable surjective étale scheme atlas. The map is `(f : X ⟶ Y)`.
- Unramifiedness is `(hunramified : MapIsLocally (@IsUnramified) f)`.
  `MapIsLocally` quantifies over every pair of schemes `U,V : Over S`, every
  representable étale chart `a : h_U → X`, `b : h_V → Y`, and each compatible
  scheme morphism `h : U → V`. Its conclusion is `IsUnramified h.left`.
  The recorded scheme definition expands to `LocallyOfFiniteType h.left ∧
  IsOpenImmersion (pullback.diagonal h.left)`. Thus the required local finite type
  is included, rather than assuming only formal unramifiedness.
- Universal injectivity is the complete binder `hinjective : ∀ (Y' : AlgebraicSpace S)
  (g : Y' ⟶ Y), Function.Injective
  (mapPoint (Limits.pullback.snd f.hom g.hom).hom)`.
  The pullback is in fppf sheaves, and its second projection is precisely
  `X ×_Y Y' → Y'`. Its algebraic-space property is supplied by the recorded
  fibre-products theorem; forming its point set does not require an extra structure.
  `mapPoint` is the canonical map on the existing field-valued point classes.
- The conclusion `IsRepresentable f.hom.hom` unfolds to `IsRepresentableWith ⊤`.
  For every `T : Over S` and `a : yoneda.obj T ⟶ Y.obj.obj`, it asserts the existence
  of a scheme `U : Over S`, projection `p : U ⟶ T`, and map `q : h_U → X`, with
  `IsPullback q (yoneda.map p) f.hom.hom a`. This says exactly that the test sheaf
  fibre product is represented by a scheme, including its projection to `T`.
  The property `⊤` imposes no further condition on that projection.

Dependency declarations read and used:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme` and `Scheme.Hom`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace`,
  `AlgebraicSpace.IsRepresentable`, `IsRepresentableWith`, and `IsEtale`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceFibreProductsEtaleCovers`:
  `AlgebraicGeometry.AlgebraicSpace.fibreProduct_isAlgebraicSpace`.
- `Sheaf.AlgebraicGeometry.AlgebraicSpacePointTopology`: the existing `Point`,
  `PointRepresentative.map`, `pointImage`, and `pointTopologicalSpace` interfaces.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceMorphismProperties`:
  `AlgebraicGeometry.AlgebraicSpace.MapIsLocally`. Its public dependency
  `Sheaf.AlgebraicGeometry.ProperCurveModuli` supplies
  `AlgebraicGeometry.AlgebraicSpace.mapPoint`, whose quotient construction was read.
- `Sheaf.AlgebraicGeometry.UnramifiedMorphism`: `AlgebraicGeometry.IsUnramified`.
- `Mathlib.AlgebraicGeometry.Morphisms.FiniteType`:
  `AlgebraicGeometry.LocallyOfFiniteType`.
- `def-weil-size-convention` has a convention record and no Lean declaration.

Available proof dependencies are imported without `public`:
`Sheaf.AlgebraicGeometry.EnlargedEtaleRingedSite` (`schemeSpace` and its named
algebraic-space proof), `Sheaf.AlgebraicGeometry.AlgebraicSpacePointOpenCalculus`
(`point_open_calculus`), and
`Sheaf.AlgebraicGeometry.SeparatedLocallyQuasiFiniteSpaceRepresentable`
(`exists_scheme_of_separated_locally_quasi_finite`). Their signatures and proof
docstrings were read. The three remaining proof nodes
`lem-sfb-space-unramified-permanence`, `lem-sfb-unramified-space-open-diagonal`, and
`lem-sfb-space-lft-monomorphism-separated-lqf` have no recorded Lean declaration in the
read repository and consequently no module to import yet. They are proof prerequisites,
not missing notions needed to type this statement. All five DAG proof steps are included
in the theorem docstring, retaining these node references for stage 3.

Edge cases checked before writing: the empty source and empty scheme tests are permitted;
identity morphisms and open immersions satisfy the stated criterion; no nonemptiness,
quasi-compactness, separatedness, finite-presentation, or field-characteristic restriction
was added. A nontrivial purely inseparable field extension is not a counterexample,
since its scheme map is not unramified. A non-quasi-compact disjoint union of open charts
is not excluded. The field-valued representatives, schemes, and test spaces retain the
same universe as the dependency framework; there is no smaller independent test universe
that could make a universal condition vacuous.

Searches performed (logged by `msearch.py`, 2026-10-24):

- LeanFinder: `An unramified universally injective morphism of algebraic spaces is
  representable by schemes` (run twice). Eight hits, including
  `AlgebraicGeometry.UniversallyInjective`, its diagonal criterion, and
  `AlgebraicGeometry.FormallyUnramified`; all concern schemes, not representability
  of algebraic-space morphisms. Read the scheme predicate and its full signature in
  `Mathlib/AlgebraicGeometry/Morphisms/UniversallyInjective.lean`.
- Loogle: `AlgebraicGeometry.AlgebraicSpace.IsRepresentable,
  AlgebraicGeometry.IsUnramified`: zero hits, unknown project identifier
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentable`. This is not evidence against
  the project definition, whose source was separately read and reused.
- Mathlib grep through `msearch.py`:
  `unramified.*(radicial|injective)|representable.*unramified|unramified.*representable`
  in `AlgebraicGeometry`: one unrelated ring-level formal-unramified injectivity proof.
- Direct `rg` of both `lean/WeilConjectures` and `lean/Sheaf` for the item id and the
  same expression found only unrelated ring-level Nakayama material and scheme/stack
  applications (`UniversalUnramifiedRadicialOpen`, `UniversalClosedImmersionOpen`,
  `DMIsomSpaceUnramified`, and related stack chart material), no theorem with this
  algebraic-space statement. A second search including the proposed declaration name
  and `MapIsUniversallyInjective` found no name conflict or reusable duplicate.
- Direct search for the item id in `lean/WeilConjectures`: no matches.

Validation: `scompile.py Q15 lem-sfb-space-unramified-radicial-representable` on the
single delivered module succeeded in both sandbox and library-module modes, with no
unexpected warnings. No global build or direct repository writes were performed.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
