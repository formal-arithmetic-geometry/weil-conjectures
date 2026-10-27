## Worker report

Item: `lem-sfb-stack-chartwise-smooth-etale-calculus`, group NP, stage 2.
Module: `Sheaf.AlgebraicGeometry.StackChartwiseSmoothEtaleCalculus`.
All eight theorem proofs are `sorry`; both definitions have complete propositional bodies.
No statement correction, disputed statement, dependency repair, or independent new notion.
The node's original statement, proof, proof dependencies and other fields are preserved.
Its statement dependencies gain four already-landed definition nodes used below.

The declaration named in `lean.declaration` is the base-change clause; `lean.declarations`
lists all ten declarations, which jointly render the complete node. The two predicates
spell out notions explicitly introduced in this item's statement, rather than creating
independent notions or replacing an existing recorded definition.

Clause and hypothesis correspondence:

- The scheme `S` is `{S : Scheme.{u}}`. Stack total categories have independent object
  and morphism universes `v₁,w₁,v₂,w₂,v₃,w₃` and lie over `Over S`.
  `IsAlgebraicModuliStack` is exactly stack descent, algebraic-space diagonal and
  existence of a smooth surjective scheme atlas. The relevant theorems bind `hF`,
  `hG`, and (for three-stack operations) `hH`. No Noetherian, quasi-compactness,
  separatedness, finiteness of the atlas, or characteristic hypothesis is imposed.
- Morphisms over `S` are `BasedFunctor`; the scheme-test 2-fibre product and projection
  are the existing `moduliTwoFiberProduct` and `moduliTwoFiberFst`.
- The five properties are selected by the explicit disjunction `hP`:
  `P = @Smooth ∨ P = @Etale ∨ P = @Flat ∨
  P = @LocallyOfFinitePresentation ∨ P = @LocallyOfFiniteType`.
  These are the actual recorded Mathlib scheme properties, not new predicates.
- `ModuliSpaceTest P f` uses an algebraic-space presentation of each actual scheme
  base change, compatible with the projection, and tests `P` on every representable
  étale scheme chart. It includes existence of the representing spaces. Its definition
  is general in `BasedCategory` and does not require the stacks to be DM.
- Representability is the recorded `IsRepresentableByAlgebraicSpaces` (`hf`, and `hg`
  for composition). `stack_chartwise_smooth_etale_calculus` permits arbitrary
  `g : BasedFunctor H G` and concludes representability and `ModuliSpaceTest P` for
  `moduliTwoFiberFst g f`. `stack_chartwise_comp` concludes both for `f.comp g`.
- Open substacks are exactly the existing `OpenModuliSubstack F`: a full subcategory
  selected by its pullback-stable predicate, whose actual scheme base changes are
  open immersions. `IsOpenModuliCover U` quantifies over every scheme map `t` and
  every point `x` of that scheme, and gives an open representing base change of some
  `U i`, with a point mapping to `x`. The comparison `IsSchemeModuliBaseChange e j`
  retains the actual projection. Thus it says the inverse images cover every scheme,
  not that a whole scheme-valued object belongs to one member.
  `stack_chartwise_openCover` gives an iff with `ModuliSpaceTest P` on each actual
  restriction `(fullModuliInclusion F (U i).property).comp f`.
- `stack_chartwise_implications` gives étale to smooth, smooth to flat and locally of
  finite presentation, and locally of finite presentation to locally of finite type.
  Étaleness is the existing `IsEtaleModuliMap`, whose definition is precisely the
  same space-test condition specialized to Mathlib's `Etale`. In particular it uses
  neither formal smoothness alone nor a different relative-dimension definition.
- `IsSurjectiveModuliMap f` explicitly quantifies over every field `K : Type u`, every
  `Spec K → S`, and every target object encoded by its map from `h_(Spec K)`.
  It produces a field `L`, a unital `K →+* L`, and a source object on `Spec L`.
  Such a field homomorphism is injective. `ModuliTwoIso` identifies the actual
  composite with restriction along `Spec.map (CommRingCat.ofHom i)`; the structural
  map to `S` is its composite with `b`. There is no arbitrary comparison morphism.
- `surjective_moduli_baseChange` and `surjective_moduli_comp` state the requested
  permanence laws with this field-lifting definition. They require no representability,
  as the node's proof step 10 expressly explains.
- `surjective_moduli_iff_chartwise` gives the equivalence for representable `f`.
  On every scheme test and every compatible presentation `HasSpaceBaseChange`, every
  étale surjective chart `a` has `Surjective (yoneda.preimage (a ≫ p)).left`.
  Both chart hypotheses are the existing algebraic-space scheme-test notions.
  Surjectivity of the resulting scheme map is the recorded Mathlib point predicate.
- For the disjoint-source clause, `I : Type z` is arbitrary, `U : I → Over S` is the
  scheme family, and `[HasCoproduct U]` asserts that its coproduct exists in this
  chosen scheme universe. In an over category, this is equivalent to the underlying
  scheme coproduct with its induced structural map to `S`. This condition does not
  require `[Small.{u} I]`, and hence includes every family whose coproduct exists
  within the bound, even with an index type in a larger universe.
  `q i` are the given maps, with exactly `IsEtaleModuliMap (q i)` as their hypothesis.
  `etale_moduli_scheme_coproduct` produces the map `a` from `h_(∐ U)` and specified
  restriction 2-isomorphisms along the actual `Sigma.ι U i`. Its conclusion states
  `IsEtaleModuliMap a` and `IsRepresentableByAlgebraicSpaces a`. This is existence of
  the descent gluing with its restriction identifications, not an arbitrary map from
  a coproduct supplied as an extra hypothesis or a choice-based definition.

Dependency declarations read and reused:

- `Sheaf.AlgebraicGeometry.StablePointedModuliGroupoids`:
  `CategoryTheory.IsModuliStack`, `IsFibredInGroupoids`, `ModuliTwoIso`,
  `moduliTwoFiberProduct`, `moduliTwoFiberFst`, `discreteModuli`, `discreteModuliMap`,
  `HasSpaceBaseChange`, `IsRepresentableByAlgebraicSpaces`, `HasAlgebraicSpaceDiagonal`,
  `SpaceMapIsEtale`, and `SpaceMapIsSurjective`. The entire signatures and docstrings
  of these definitions were read in the published local source.
- `Sheaf.AlgebraicGeometry.AlgebraicSpace`: `AlgebraicGeometry.AlgebraicSpace` and
  `AlgebraicGeometry.AlgebraicSpace.IsRepresentableWith`, `IsRepresentable`,
  `IsEtale`, `IsSurjective`, `IsAlgebraicSpace`, with their scheme-test definitions.
- `Mathlib.AlgebraicGeometry.Morphisms.Smooth`: `AlgebraicGeometry.Smooth`;
  `...Etale`: `AlgebraicGeometry.Etale`; `...Flat`: `AlgebraicGeometry.Flat`;
  `...FinitePresentation`: `AlgebraicGeometry.LocallyOfFinitePresentation`;
  `...FiniteType`: `AlgebraicGeometry.LocallyOfFiniteType`. Full class signatures,
  ambient scheme binders and affine-local conditions were read.
- `Mathlib.AlgebraicGeometry.OpenImmersion`: `AlgebraicGeometry.IsOpenImmersion`;
  `Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap`: `AlgebraicGeometry.Surjective`.
- `Mathlib.AlgebraicGeometry.Limits`: the small-family coproduct existence instance,
  `AlgebraicGeometry.sigmaOpenCover`, `AlgebraicGeometry.disjoint_opensRange_sigmaι`.
  The signatures expose `[Small.{u} σ]`; our conclusion is conditional on the
  coproduct existing, and does not impose that sufficient condition as necessary.
- `def-weil-size-convention` has a metatheoretic convention record, not a declaration.
  The explicit scheme, stack and index universes implement it.
- Four already-landed owning nodes are added to `stmt_deps` (no duplicate modules):
  `def-sfb-algebraic-moduli-stack` supplies
  `Sheaf.AlgebraicGeometry.AlgebraicModuliStack.IsAlgebraicModuliStack`
  (declaration namespace `CategoryTheory`);
  `def-sfb-dm-stack-morphism-properties` supplies
  `CategoryTheory.ModuliSpaceTest` in `Sheaf.AlgebraicGeometry.DmStackMorphismProperties`;
  `def-sfb-open-moduli-substack` supplies `CategoryTheory.OpenModuliSubstack` and
  `fullModuliInclusion` in `Sheaf.AlgebraicGeometry.OpenModuliSubstack`;
  `def-sfb-moduli-chart-normalization` supplies `CategoryTheory.IsSchemeModuliBaseChange`
  and `IsEtaleModuliMap` in `Sheaf.AlgebraicGeometry.ModuliChartNormalization`.
  Each owning node's statement and Lean record and the declarations' complete
  signatures and docstrings were read. These notions already occur in the item's prose.

Proof imports retain the recorded scheme-locality and presentation-criterion modules,
`AlgebraicSpaceFibreProductsEtaleCovers`, `EtaleSmoothZeroDimensionalFibres`, Mathlib
`Proper`, and the closed upstream `SmoothFiber` theorem recorded for `lem-pc-smooth-flat`.
Other scheme permanence inputs are in the imported Mathlib property modules.
`lem-sfb-representable-pullback-over-space` has no Lean binding in the read DAG, so there
is no module for that proof-only dependency to import. It is not a missing notion in
our signatures. No downstream theorem is imported and no dependency wait is introduced.

Edge cases checked before drafting and again on the final statements:

- Empty source or target: chart properties have their usual empty-scheme meaning;
  field lifting has no target object to lift when the target is empty.
- Empty open covering family is permitted. Its covering condition can hold only
  when every test scheme mapping to the source is empty; the locality iff retains
  the vacuous right side in exactly this case.
- Empty coproduct index set is permitted by `[HasCoproduct U]`; stack descent on
  the empty cover supplies the map from the empty scheme, and étaleness is vacuous.
- Infinite families, non-quasi-compact charts, inseparable field extensions and
  every characteristic are allowed; no prime, algebraic-closure, or finite-type
  restriction is imposed on the fields in the lifting condition.
- Independent stack object and arrow universes are retained. Test fields are in the
  scheme universe `u`, not in a smaller independent universe. The index universe `z`
  is independent and the only coproduct size condition is actual existence.
- A scheme mapping to a stack can straddle several source opens: the cover predicate
  is pointwise on inverse images and does not demand membership in one open.

Searches for an existing full statement or definitions:

- `msearch.py ... leanfinder "Representable morphisms of algebraic stacks smooth etale
  flat stability base change composition open source locality"`: eight hits, all
  scheme-level smooth/étale/flat definitions or permanence facts; no stack calculus.
- `msearch.py ... loogle "AlgebraicGeometry.Smooth, AlgebraicGeometry.Etale"`: one hit,
  `AlgebraicGeometry.Etale.instSmooth`, the scheme implication only.
- `msearch.py ... grep "IsAlgebraicStack|OpenSubstack|RepresentableByAlgebraicSpaces"
  AlgebraicGeometry`: zero Mathlib hits.
- `msearch.py ... leansearch "surjective morphism of algebraic stacks field extension
  local lifting"`: eight hits, including `AlgebraicGeometry.Surjective` and scheme
  flat-descent/surjective-on-stalks facts; no field-lifting predicate on stack maps.
- `rg` in `lean/WeilConjectures` for the item id returned no declaration. Searches in
  both `lean/WeilConjectures/AlgebraicGeometry` and `lean/Sheaf/AlgebraicGeometry` for
  `ModuliSpaceTest`, `IsAlgebraicModuliStack`, `OpenSubstack`, `OpenModuliSubstack`,
  `SpaceMapIsSmooth`, chartwise smoothness, field-lifting and open-cover definitions
  found the existing interfaces reused above. Searches for the two new helper names
  and theorem names found none. No existing full statement was found.

Sources opened locally: stacks-properties.tex Section 04XB and the actual
`lemma-property-spaces-too`, `lemma-composition-surjective`, `lemma-base-change-surjective`
statements; algebraic.tex `lemma-composition-representable-transformations-property`,
`lemma-base-change-representable-transformations-property`, and
`lemma-representable-diagonal`. The original node's complete 13-step proof is preserved;
each theorem docstring carries the relevant steps verbatim, with dependency names.

Validation: prescribed `scompile.py` compiled the module both as sandbox and library
module with no errors or warnings (9.3 s and 7.8 s on the first pass). Subsequent dry-run
validation covers the final imports and complete delivery. No live source or git mutation
was performed directly; only the authorized sandbox and launcher wrappers were used.

## Second reading by NP

A separate second pass by this worker read the final node and module clause by clause.
No subagent was started, as required by this dispatch; the maintainer supplies the
independent review. The match checked includes the five exact scheme predicates,
representability in both permanence conclusions, both directions of open-source locality,
all four implications, surjectivity without representability, the every-chart equivalence,
and the coproduct map's actual restriction 2-isomorphisms. Definitions are fully written,
all universes are bound, and all theorem bodies are only `sorry`.

The second pass checked two possible overrestrictions explicitly: using whole-object
membership in one source open would exclude maps crossing several opens, so the delivery
uses inverse-image point covering; requiring a small index type would be stronger than
existence of the coproduct in the chosen universe, so the delivery uses `[HasCoproduct U]`.
It also added the explicit upstream `SmoothFiber` proof import corresponding to the
recorded closed smooth-flat input. No mathematical mismatch remains and the node's
statement is unchanged. There are no new nodes or dependency modules to review.
