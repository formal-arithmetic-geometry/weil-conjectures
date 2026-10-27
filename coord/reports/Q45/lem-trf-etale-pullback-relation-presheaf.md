## Worker report

The module `Sheaf.AlgebraicGeometry.EtalePullbackRelationPresheaf` states
`AlgebraicGeometry.AlgebraicSpace.etale_pullback_relation_presheaf`. It has one
postponed theorem and no definitions or auxiliary postponed declarations. The
node changes only in `lean`; its statement and accepted split are unchanged.

Sources read: Spaces Tag 02WT, `lemma-pullback-etale-equivalence-relation`;
Groupoids Tags 02V8/02V9, `lemma-restrict-relation` and
`definition-restrict-relation`; and Tag 045Z,
`lemma-quotient-pre-equivalence-relation-restrict`, including the preceding
explanation that the quotient presheaf is the sectionwise equivalence-relation
quotient. The theorem docstring gives all five steps of the node's proof.

Hypotheses and objects, in order:

- The base scheme is `{S : Scheme.{u}}`, and the three schemes over it are
  `{R U U' : Over S}`. Morphisms in `Over S` are precisely scheme morphisms
  commuting with the maps to S. Test schemes are all `T : Over S`, so every
  occurrence of a section means a morphism over S.
- The two arrows are `(s t : R ⟶ U)`. The monomorphism into the fibre product
  is `[Mono (prod.lift s t)]`. Products in `Over S` are fibre products over S.
- The hypothesis `hrel` is exactly the equivalence of the relation
  `∃ r : T ⟶ R, r ≫ s = a ∧ r ≫ t = b`, for every test scheme T.
- The refinement is `(g : U' ⟶ U)` and the three étale hypotheses are
  `[Etale s.left] [Etale t.left] [Etale g.left]`. No surjectivity, injectivity,
  affineness, or separatedness hypothesis is imposed on g or the schemes.
- The node's A is the literal Mathlib object `pullback g s`. Its R' is
  `pullback (pullback.snd g s ≫ t) g`. Working in `Over S` constructs the same
  iterated scheme fibre product with its structural map to S.

Conclusions, in order:

- `s'`, `t'`, and `r'` are existentially named morphisms with three equalities
  fixing them to the first, last, and middle projections of that literal
  iterated pullback. They are fixed canonical constructions, not arbitrary
  arrows or new assumptions. No new definition of the restricted relation is
  introduced.
- The first quantified biconditional says precisely that compatible triples
  `(a,r,b)` correspond to exactly one map `z` into R', with all three
  coordinates specified by `z ≫ s'`, `z ≫ r'`, `z ≫ t'`. This is the natural
  identification on test schemes: each coordinate is postcomposition with a
  fixed projection, hence is a component of its Yoneda natural transformation.
  These natural coordinate maps and the unique-map characterization specify
  the natural bijection, not an unrelated bijection for each test scheme.
- The next clause explicitly says `r₁ = r₂` for any two arrows with the
  prescribed pair of endpoints `(a ≫ g,b ≫ g)`.
- `Mono (prod.lift s' t')` is the restricted monomorphism into U' ×_S U'.
- The following biconditional identifies existence of a restricted-relation
  witness with existence of an original-relation witness at `a ≫ g,b ≫ g`.
- The following `Equivalence` clause says the restricted relation on every
  U'(T) is an equivalence relation.
- `Etale s'.left ∧ Etale t'.left` states both projection claims.
- P and P' are `coequalizer (yoneda.map s) (yoneda.map t)` and the analogous
  coequalizer for s',t', in presheaves of sets. Their quotient maps q and q'
  are `coequalizer.π`. The two `Function.Surjective` clauses assert
  surjectivity on sections at every `op T`, not just categorical epimorphy.
- The two equality-of-classes biconditionals specify that equality after q
  (respectively q') is exactly the given equivalence relation. Together with
  surjectivity these identify the coequalizers with precisely U(T)/~ and
  U'(T)/~'. This is the standard categorical presentation of the quotients
  named in the node, not an extra mathematical conclusion or a changed notion.
- Restrictions are the maps of those presheaves. Their value on a class is
  the class of the precomposition: the naturality of the coequalizer
  projection says `P(c)(q_T(a)) = q_T1(c ≫ a)`, and its stated surjectivity
  determines restrictions on all sections. Thus the node's restrictions and
  natural quotient projections are retained by using presheaf coequalizers.
- The last existential is a natural transformation `v : P' ⟶ P`. Its first
  clause reads `v_T(q'_T(a)) = q_T(a ≫ g)`, exactly the formula on classes.
  Its next clause is `Function.Injective (v.app (op T))` for every T.
  Its final equality is `q' ≫ v = yoneda.map g ≫ q`, the node's commuting
  square in Lean's left-to-right composition convention. `yoneda.map g` is h_g.

Dependency declarations used:

- `def-pc-scheme`: `Mathlib.AlgebraicGeometry.Scheme`, declarations
  `AlgebraicGeometry.Scheme` and `AlgebraicGeometry.Scheme.Hom` (full
  definitions and docstrings read in Scheme.lean).
- `def-pc-fibre-product`: `Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback`,
  declarations `CategoryTheory.Limits.pullback`, `.fst`, `.snd`, `.lift`,
  `.isLimit`, and the universal property, read in that source. Scheme pullbacks
  come from `Mathlib.AlgebraicGeometry.Pullbacks`; products and pullbacks in
  `Over S` encode the specified relative scheme fibre products.
- `def-weil-etale-morphism`: `Mathlib.AlgebraicGeometry.Morphisms.Etale`,
  declaration `AlgebraicGeometry.Etale`, with its full affine-local definition.
- The two proof-dependency Mathlib leaves are already supplied by the same
  Étale import: `Etale.etale_comp` and the pullback-projection instances. I
  also read `Etale.of_comp`, the open-immersion instance, the
  `MorphismProperty.Over.pullback` functor, `mkIdTerminal`, and finite-limit
  preservation in `CategoryTheory.Limits.MorphismProperty`. No unusable
  dependency record needs repair.
- The remaining public imports are the Mathlib type-colimit and functor-category
  instances providing the presheaf coequalizers. All proof dependencies with
  usable statements are therefore covered by the module's imports.

Existing-definition searches:

- `msearch.py`, LeanFinder: "Pullback of an etale scheme equivalence relation
  induces an injective map of quotient presheaves". Eight hits on étale
  categories, their forgetful functors, and scheme-gluing injectivity; none
  states this combined result.
- `msearch.py`, Loogle: `Setoid.comap, Quotient.map,
  CategoryTheory.Limits.pullback.lift`. Zero hits for that combined query.
- `msearch.py`, grep: `equivalence.*relation|quotient.*presheaf` in
  `AlgebraicGeometry`. One hit: Gluing.lean's relation on a disjoint union,
  not this theorem.
- `msearch.py`, LeanSearch: "Quotient presheaf of an equivalence relation is
  the coequalizer and the quotient map is surjective on each object". Eight
  hits include `Quotient.mk_surjective` and `Function.Coequalizer.mk_surjective`,
  which are ingredients, not this statement.
- Direct `rg` over `lean/WeilConjectures` and `lean/Sheaf` for relation,
  quotient-presheaf, and pullback-relation names found the existing modules
  `EtaleRelationRestrictionQuotient` and `EtaleRelationQuotient`. I read their
  declarations: the first states a sheafification result rather than this
  sectionwise presheaf statement; the second defines the map to a sheafified
  quotient and states representability, not this node. The former's three
  named restricted-relation helpers live in a downstream consumer. Importing
  it here would reverse the proof-dependency direction. I use Mathlib's raw
  pullbacks directly and introduce no duplicate helper definition. Its later
  proof can instantiate this theorem using its definitionally identical
  projections. No import cycle is introduced.
- Direct searches of Mathlib CategoryTheory and AlgebraicGeometry for quotient
  presheaves, relation setoids, and coequalizers found generic constructions.
  The type colimit source and Function.Coequalizer source were read. They do
  not assert the scheme relation and étale conclusions together.
- Direct `rg` of the node id in `lean/WeilConjectures` and
  `dag/lean_names_upstream.json`, and of the proposed full declaration's
  terminal name in Mathlib, WeilConjectures, Sheaf and the upstream name index,
  found no existing declaration for this item or collision with its name.

Edge cases checked: R, U, U', or a set of test-scheme sections may be empty;
no witness is demanded when the endpoints do not exist. Surjectivity of a
quotient of an empty set is valid. In the discrete relation the restricted
relation is the kernel relation of g, so injectivity of the quotient map does
not require g to be a monomorphism. If g is the identity, both quotients agree;
if g has empty source the injection is from the empty quotient on nonempty
T. The empty test scheme is still quantified, and its unique maps satisfy
reflexivity. There is no positivity, characteristic, or nonemptiness
restriction. `u` is arbitrary and all scheme Hom types have universe u;
`Over S` has object universe u+1 and morphism universe u, so no independent
smaller test universe or inappropriate smallness assumption is introduced.

Validation: the prescribed scompile.py compiled the module in both sandbox
and library modes without errors or warnings (20.8 s and 8.9 s). The sole
proof is `by sorry`, as required for stage 2. The exact signature is copied
into `lean.statement`; all lines have at most 100 characters. No new nodes,
dependency repairs, statement corrections, or disputed statements.

The worker re-read the node and the final signature after compilation:
every assumption and clause above is present, the quotient maps have the
correct source and target, and composition is consistently over S. No
mismatch required a change. The maintainer's independent review is still
the independent reading, according to the direct-delivery brief.

## Second reading by Q45

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
