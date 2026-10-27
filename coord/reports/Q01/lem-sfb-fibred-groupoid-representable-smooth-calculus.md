## Worker report

The module `Sheaf.AlgebraicGeometry.FibredGroupoidRepresentableSmoothCalculus`
states the node in five named theorems, all with `by sorry`. It defines no new
notion and changes no natural-language statement. The original node is preserved
except for its Lean record and four added, already landed definition dependencies.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

- The base is `{S : Scheme.{u}}`. Tests are `T : Over S`. The three input categories
  are `BasedCategory.{v₁, w₁} (Over S)`, `BasedCategory.{v₂, w₂} (Over S)` and
  `BasedCategory.{v₃, w₃} (Over S)`: all six category universes are independently
  bound. The existing algebraic-space and test-field constructions use universe
  `u`, as does the big scheme site. `set_option autoImplicit false` prevents
  implicit introduction of variables or universe levels.
- “Categories fibred in groupoids” is exactly `IsFibredInGroupoids`, supplied as
  `hF`, `hG`, and, where relevant, `hH`. Its definition combines a fibrewise lift
  with strong cartesianness of every arrow, including unique factorization.
  There is no `IsModuliStack`, `IsAlgebraicModuliStack`, diagonal condition or
  chosen atlas in any binder. The base-changing category also has only `hH`.
- Morphisms are the recorded `BasedFunctor`s. Composition is `f.comp g`.
  The pullback projection is `moduliTwoFiberFst g f`, from the recorded
  `moduliTwoFiberProduct g f` to `H`. The reversed order of the two factors
  places the base-changing category first, exactly as in the recorded scheme
  test interface. Comparisons are actual `ModuliTwoIso`s over the base, not
  equivalence of sets of isomorphism classes.
- Representability by spaces is the existing
  `IsRepresentableByAlgebraicSpaces`. It quantifies over **every** `T` and
  `t : BasedFunctor (discreteModuli (yoneda.obj T)) G`, and supplies a space `Z`,
  its actual projection `p`, and `HasSpaceBaseChange f T t Z p`. The latter
  retains an equivalence and a 2-isomorphism with the projection to `h_T`.
- Smoothness is the existing `ModuliSpaceTest @Smooth f`: each scheme test has
  a space representation and every representable étale scheme chart has
  smooth composite to the test scheme. Thus the map is representable as part
  of this property. This is the node's source-chart convention over a scheme.
- Étaleness is the existing `IsEtaleModuliMap f`, supplying the same tests and
  `SpaceMapIsEtale` on their projections; that predicate universally tests
  étale scheme charts. It also includes representability.
- The opening definition of surjectivity on the space projections is rendered
  explicitly in `fibred_groupoid_surjective_iff_space_tests`. Its right side
  quantifies over every scheme test and asks for `HasSpaceBaseChange` and
  `AlgebraicSpace.IsJointlySurjective (fun _ : Unit ↦ p)` for its actual
  projection. The singleton family says exactly that the image on field-point
  classes is the whole target. `IsJointlySurjective` retains a field extension
  `K →+* L` and equality of the restricted section; this is the common-extension
  point-class convention, with no scheme-representability assumption on `p`.
  The left side identifies this definition with representability and the
  already recorded `IsSurjectiveModuliMap f`. The latter retains the actual
  lifted object, field extension, restriction map and 2-isomorphism. Consequently
  the surjectivity clauses below use the same notion the node introduces.
- `fibred_groupoid_representable_baseChange` has four conjuncts: representability
  of the projection, preservation of smoothness, preservation of étaleness,
  and preservation of surjectivity. The only condition on the map `g : H → G`
  is that it is a functor over the base; it need not be representable, smooth,
  étale or surjective.
- `fibred_groupoid_representable_comp` has four analogous conjuncts for `f.comp g`.
  Its `hf`, `hg` state exactly the representability of both input maps.
  Each property implication assumes that property for both maps.
- `fibred_groupoid_etale_smooth` concludes `ModuliSpaceTest @Smooth f` from
  `IsEtaleModuliMap f`. Its input already includes representability, so there
  is no independent or stronger representability hypothesis.
- `space_discrete_moduli_comparison` takes arbitrary `G F : AlgebraicSpace S`
  and `f : G ⟶ F`. Its first conjunct asserts space-representability of
  `discreteModuliMap f.hom.hom`, with no extra hypothesis. Its second conjunct
  assumes exactly `AlgebraicSpace.IsRepresentable f.hom.hom`, meaning
  scheme-representability, and then gives BOTH requested equivalences:
  `AlgebraicSpace.IsEtale` iff `IsEtaleModuliMap`, and
  `AlgebraicSpace.IsSurjective` iff `IsSurjectiveModuliMap`. The old surjectivity
  predicate is the recorded scheme-test topological one. This universal
  assertion includes scheme charts: their source is a scheme algebraic space,
  and their maps are scheme-representable by the algebraic-space definition.

Dependency interfaces read and reused:

- `Mathlib.AlgebraicGeometry.Scheme`: `AlgebraicGeometry.Scheme`, its morphisms
  and the `Over S` category (`def-pc-scheme`). The size-convention node has
  no declaration; its explicit universe discipline is implemented by the binders.
- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsFibredInGroupoids`, `ModuliTwoIso`, `moduliTwoFiberProduct`,
  `moduliTwoFiberFst`, `discreteModuli`, `discreteModuliMap`,
  `HasSpaceBaseChange`, `IsRepresentableByAlgebraicSpaces`, `SpaceMapIsEtale`.
  Full definitions and their source docstrings were read. Their types do not
  impose a stack condition despite the name of the owning module.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`:
  `AlgebraicGeometry.AlgebraicSpace`, `IsRepresentableWith`, `IsRepresentable`,
  `IsEtale`, `IsSurjective`. Space morphisms are the recorded natural
  transformations; `f.hom.hom` is their underlying presheaf transformation.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `Mathlib.AlgebraicGeometry.Morphisms.Etale`: `AlgebraicGeometry.Etale`;
  `Mathlib.Algebra.Field.Defs`: `Field` through the existing field-point predicates.
- `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`:
  `CategoryTheory.ModuliSpaceTest`. Its full signature and definition were read;
  it applies to arbitrary based categories, without a DM hypothesis. Its owning
  node `def-sfb-dm-stack-morphism-properties` is added to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.ModuliChartNormalization`:
  `CategoryTheory.IsEtaleModuliMap`. Its owning node
  `def-sfb-moduli-chart-normalization` is added to `stmt_deps`.
- `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`:
  `CategoryTheory.IsSurjectiveModuliMap`, read with its full field-extension and
  actual `ModuliTwoIso` comparison. The owning definition node
  `def-sfb-surjective-moduli-map` is already landed and added to `stmt_deps`.
  The module's stack calculus theorems are not used as replacement statements:
  they assume algebraic stacks, so they do not state this arbitrary-CFG node.
- `Sheaf.AlgebraicGeometry.AlgebraicSpaceJointSurjectivity`:
  `AlgebraicGeometry.AlgebraicSpace.IsJointlySurjective`. Its owning node
  `def-trf-algebraic-space-jointly-surjective-family` is added to `stmt_deps`.

The stated proof dependencies are imported privately: scheme étale locality,
the space presentation criterion, space fibre products/étale covers,
representable étale scheme tests, and étale-smooth-zero-dimensional fibres.
The smooth and étale Mathlib imports also supply their composition leaves;
private `PullbackCarrier`, `ResidueField`, and `Morphisms.UnderlyingMap` supply
the remaining scheme inputs. `lem-sfb-representable-pullback-over-space` has
no recorded Lean declaration in the current node and is therefore not imported.
It is a proof prerequisite, not a missing object required to type this statement.
Its use remains in the unchanged composition proof and theorem docstring; no
replacement theorem or unsupported construction was introduced.

Sources read: local Stacks `algebraic.tex`, labels
`lemma-base-change-representable-by-spaces` (0302),
`lemma-composition-representable-by-spaces` (0301),
`lemma-map-presheaves-representable-by-spaces-transformation-property` (045A),
`lemma-composition-representable-transformations-property` (045B), and
`lemma-base-change-representable-transformations-property` (045C), together
with the accepted seven-step DAG proof. These sources explicitly use CFGs;
no stack hypothesis was imported from a stronger calculus result. Each theorem's
source docstring contains the relevant complete natural-language argument,
including triple reassociation, the compatible chart composition, the two
successive field extensions, and the residue-field argument for the comparison.

Edge cases checked before writing:

- Empty test schemes and empty source/target groupoids are admitted. Point-lifting
  conditions are vacuous over empty targets; an empty source cannot supply a
  point over a nonempty field test. No `Nonempty` hypothesis was added.
- Identity maps and tests with identity comparison are included. No choice of
  chart or atlas is part of an input, so empty spaces are also covered.
- Nontrivial automorphisms and a base-changing CFG failing descent remain in
  the quantifiers. Their full 2-fibre products are used; no replacement by a
  quotient set or stackification occurs.
- Characteristic is unrestricted; no Noetherian, separated, finite-type or
  quasi-compact assumption is present.
- The six object/morphism universes are independent, while scheme test fields
  remain in the scheme universe. The singleton point-image family is `Unit`,
  not a nonempty atlas assumption or a restricted collection of points.

Searches for existing statements and notions (2026-10-24):

- `msearch.py ... leanfinder`: “Morphisms of categories fibred in groupoids
  representable by algebraic spaces smooth etale surjective stable under
  composition and arbitrary 2 base change”. Eight hits, all scheme results:
  smooth-composition, étale-base-change, scheme étale pretopology, etc.; no CFG
  calculus statement.
- `msearch.py ... loogle '"relativelyRepresentable"'`: twelve hits in
  `Mathlib.CategoryTheory.MorphismProperty.Representable`, including ordinary
  relative representability and its stability instances. They use ordinary
  categorical pullbacks and do not state this 2-fibre-product calculus.
- `msearch.py ... grep 'Fibred.*Groupoid|Representable.*Smooth|Smooth.*Representable'`:
  zero Mathlib hits.
- `msearch.py ... leansearch`: “Representable morphisms of fibered groupoids
  preserve smooth etale surjective under composition and two pullbacks”. Eight
  hits: scheme étale cancellation, ordinary relative morphism-property
  composition, and ring formal smoothness. None states the node.
- `rg` over `lean/WeilConjectures` for the item identifier: no hit. Searches for
  `IsRepresentableByAlgebraicSpaces`, `SpaceMapIsSmooth`, `ModuliSpaceTest` and
  representable smoothness in `lean/WeilConjectures` and `lean/Sheaf` located the
  reused definitions and the stronger stack calculus above. Searches of the
  DAG identified the owning landed definition nodes, avoiding duplicate notions.
- The five chosen theorem names were searched in `lean/Sheaf`,
  `lean/WeilConjectures`, and `dag/lean_names_upstream.json`; no existing name or
  exact arbitrary-CFG calculus declaration was found.

Validation: the prescribed server `scompile.py` compiled the delivered module
both as sandbox source and as its library module. Both succeeded, with no
errors or warnings (5.9 s and 4.3 s respectively). All five proofs are `sorry`;
no proof or definition data was supplied. No disputed statement, correction,
new node or dependency repair is needed.

## Second reading by Q01

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
