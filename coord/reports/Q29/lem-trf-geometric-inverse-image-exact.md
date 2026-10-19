## Worker report

The delivery states `CategoryTheory.GeometricMorphism.geometric_inverse_image_exact` in
`Sheaf.CategoryTheory.Sites.GeometricInverseImageExact`. Its only theorem proof is `sorry`.
It adds the real structure definition `CategoryTheory.AbelianInverseImagePresentation` in
its own definition node and module. No definitions contain postponed data or proofs.
No natural-language statement was corrected and no dependency record was replaced.

The source is Stacks, Modules on Sites 04JC, first assertion; Sites 00YR and 00YV (2);
and Modules on Sites 03D2, 03DA and 03DB. I read the local source at
`lemma-flat-pullback-exact`, `lemma-pullback-module`, and
`proposition-functoriality-algebraic-structures-topoi`. The second assertion of 04JC,
about extension to a different coefficient ring, is not the assertion of this node.
The transported target ring is the actual inverse image ring, presented with all its
operations by the recorded `AlgebraicInverseImageOfUniverses` interface.

Hypotheses and clauses, in order:

- The small sites C and D are the independent binders `{C : Type uC}`, `{D : Type uD}`,
  `[Category.{vC} C]`, `[Category.{vD} D]`, with topologies `J` and `K`. Relative smallness
  is `[EssentiallySmall.{w} C]` and `[EssentiallySmall.{w} D]`, where `w` is the sheaf
  value universe. Every small site has such a presentation; object and morphism
  universes are not identified. Grothendieck topologies and `Sheaf` are the site/sheaf
  components of the recorded sites-and-cohomology definition. Arbitrary sites are
  allowed, not only sites presented by a particular continuous functor.
- The geometric morphism is
  `f : GeometricMorphism (Sheaf K (Type w)) (Sheaf J (Type w))`.
  The recorded structure supplies precisely `f.inverse`, `f.direct`, `f.adj`, and
  `f.leftExact`, in the direction in the node: inverse image goes from J to K.
- The induced abelian inverse image is an
  `A : AbelianInverseImagePresentation f.inverse`. Its functor is between the actual
  `Sheaf J AddCommGrpCat.{w}` and `Sheaf K AddCommGrpCat.{w}` categories. `A.underlying`
  identifies its underlying sheaf naturally with `f.inverse` on underlying sheaves.
  `A.map_add` and `A.map_zero` impose transport of operations on EVERY test sheaf and
  EVERY section. Product tests give the usual product-comparison formula; zero and
  negation are forced. Thus the lift is normalized, not an arbitrary functor over a
  set-level map. The first conjunct asserts existence of such a lift and its exactness.
  The second conjunct states exactness for every such normalized presentation, so
  consumers with already chosen canonical presentations can use the theorem directly.
  These are existence and independence of presentation of the induced functor;
  neither an extra hypothesis nor a choice of data from an unspecified existence proof.
- Exactness is literally Mathlib `exactFunctor _ _ A.functor`, i.e. preservation of
  finite limits AND finite colimits. This is the recorded definition of exact functor,
  and includes kernels, cokernels and zero. In these abelian categories it is also
  exactness on short exact sequences.
- The coefficient sheaf is quantified as `B : Sheaf J CommRingCat.{w}`, without any
  nonzero, flatness, constant-coefficient or scheme assumption.
- A presentation of the transported ring is `BI : Sheaf K CommRingCat.{w}` with
  `I : SheafOfModules.AlgebraicInverseImageOfUniverses f.inverse B BI`. This is the
  existing dependency definition; it specifies the natural ring comparison and all
  ring and module operations, including the scalar action. Its ULift presentation
  uses the same value universe `w`; it does not change the groups or actions.
  The existence clause provides `BI` and this normalized transport for EVERY `B`.
  Subsequently exactness is quantified over EVERY `BI,I`, not only that witness.
- The module functor is `I.modules` between the genuine Mathlib `SheafOfModules`
  categories, definitionally the recorded `ringedSiteModules`. The conclusion
  `exactFunctor _ _ I.modules` includes preservation of finite limits and cokernels,
  hence the relation-presentation cokernels named in the node.
- Exactness on underlying abelian sheaves is the separate conclusion
  `exactFunctor _ _ (I.modules ⋙ SheafOfModules.toSheaf (... BI))`.
  Thus it is stated as exactness of a functor into abelian sheaves, with the actual
  scalar-forgetting functor. The target ring is exactly `BI`, which is normalized as
  `f.inverse B`; there is no tensor extension to a different ring and no flatness
  assumption.

Dependency declarations read and used:

- `Sheaf.CategoryTheory.Sites.GeometricMorphism`, `CategoryTheory.GeometricMorphism`.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`, and its documented retained
  `GrothendieckTopology`, `Precoverage.toGrothendieck`, and `Sheaf` components.
- `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`, the
  transparent abbreviation of `SheafOfModules`; the latter's `toSheaf` is used.
- `Mathlib.CategoryTheory.Limits.ExactFunctor`, `CategoryTheory.exactFunctor` and
  `exactFunctor_iff`; `Mathlib.CategoryTheory.Limits.Preserves.Finite`,
  `CategoryTheory.Limits.PreservesFiniteLimits` and `PreservesFiniteColimits`.
- `Sheaf.CategoryTheory.AlgebraicInverseImageOfUniverses`,
  `SheafOfModules.AlgebraicInverseImageOfUniverses`, as recorded by
  `def-weil-pbc-algebraic-inverse-image`. This existing landed node is added to
  statement dependencies; no second ring/module transport is defined.
- The new definition node `def-trf-abelian-inverse-image-presentation`, below.

The theorem docstring carries all five proof steps, with the node names. Proof imports
provide `Adjunction.leftAdjoint_preservesColimits` and
`Adjunction.rightAdjoint_preservesLimits` (Adjunction.Limits, already imported by the
geometric-morphism dependency); `Adjunction.mapCommGrp` and `Functor.mapCommGrp`
(Monoidal.CommGrp_); `sheaves_algebraicStructures_objects`
(Sheaf.CategoryTheory.SheavesAlgebraicStructuresObjects); sectionwise sheaf limits
(`Sheaf.createsLimitsOfShape`, Sites.Limits); left exact sheafification
(`HasSheafify.isLeftExact`, Sites.Sheafification/LeftExact); the abelian/enough-injective
category declarations (Sites.Abelian and Abelian.GrothendieckCategory.EnoughInjectives);
and `CategoryTheory.moduleSheaves_colimits_forgetful`
(WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful). The last module was
read with `scompile.py --source`, since its current published source is not at the old
local path. Its full signature and docstring give faithfulness, finite limits, finite
colimits and all small limits/colimits, exactly as the proof uses.

Edge cases checked mathematically before writing: the zero module and zero abelian
sheaf are allowed, and exactness preserves them; the zero commutative ring is allowed;
empty diagrams include terminal and initial objects; empty sites and degenerate topoi
are allowed whenever the geometric morphism datum exists; the identity and composites
are included because the theorem is for arbitrary `f`; no points or enough-points
assumption is used. Non-flat ring extensions do not contradict this statement because
there is no extension beyond the transported ring. The module and abelian presentation
fields contain no exactness or adjunction assumption, so the conclusions are not built
into their inputs. The existence clauses prevent vacuity from an absent presentation.

Searches (recorded by msearch.py in this sandbox):

- LeanFinder: `A geometric morphism inverse image transports abelian sheaves and
  modules over its inverse image ring exactly`: eight site-functor pullback hits,
  including `SheafOfModules.pullback`, `pullbackIso`, and
  `pullbackPushforwardAdjunction`. These require a continuous functor of the given
  sites and do not state the arbitrary-geometric-morphism theorem.
- Loogle: `CategoryTheory.Functor.mapCommGrp,
  CategoryTheory.Limits.PreservesFiniteLimits`: one hit,
  `AddCommGrpCat.leftExactFunctorForgetEquivalence.unitIsoAux`; this is not the node's
  exactness assertion on sheaves and modules.
- Mathlib grep: `mapCommRing|mapRing|inverseImageAb|geometric.*[Ee]xact` in
  CategoryTheory: zero hits.
- LeanSearch: `lift a finite limit preserving functor of sheaves of sets to abelian
  sheaves with normalized underlying sheaf and addition`: eight hits, including
  `sheafIsAbelian`, `HasSheafify.mk`, module/presheaf forgetful exactness and
  sheafification exactness; none supplies the normalized general inverse-image lift.
- LeanFinder: `A functor on sheaves of abelian groups with a natural underlying set
  inverse image isomorphism preserving addition and zero on every generalized section`:
  eight hits including `SheafOfModules.toSheaf`, `sheafForget`, and site-specific
  pullbacks/pushforwards; no standalone abelian lift presentation.
- Mathlib grep: `AbelianSheafInverseImage|AbelianInverseImage|abelian.*inverse.*[Ll]ift`
  in CategoryTheory: zero hits.
- Upstream/project `rg` by `geometric.*[Ee]xact`, `inverseImageAb`, `geometricModule`,
  the actual item id, and the proposed declaration names: no duplicate theorem.
  Project search found the existing algebraic inverse-image interfaces, which are
  reused, and `ConstantLeftModuleInverseImageLift`, which contains an abelian lift
  inside constant-coefficient module, adjunction, exactness and coherence data.
  It cannot stand for a standalone normalized abelian presentation with no such extra
  fields. Scheme-specific `scalarAbelianInverseImage` and
  `moduleAbelianInverseImageComparison` likewise do not define the general notion.
- DAG `rg -l` and `blueprint_refs.py search 'abelian inverse image'`: the only blueprint
  result was `sk-lem-pe-injective-acyclicity`, not a definition of this notion.
  `blueprint_refs.py search 'algebraic inverse image'` gave no blueprint result;
  the existing extra node was found in the DAG and reused. `blueprint_refs.py ancestor`
  identified `lem-trf-local-term-locality` for the new node's ancestry. The broader
  inverse-image search gave specialized scheme, coefficient, and cohomology nodes.

There is no STATEMENT-DISPUTED flag and no source statement fault.

## New nodes

`def-trf-abelian-inverse-image-presentation` defines only the normalized abelian lift
needed to name the induced functor. Source: Stacks Sites 00YR and 00YV (2). Its data
are an actual functor, a natural underlying-sheaf isomorphism, and addition/zero graph
conditions on all generalized sections. It does not include any exactness, adjunction,
chosen section lifts, or module coefficients. The three kinds of recorded Mathlib
search, upstream/project searches and DAG/blueprint searches above found no existing
standalone declaration. The definition reuses the existing `Sheaf`, `AddCommGrpCat`
and `sheafCompose`; it introduces no copy of those notions. Its universe variables
for the two sites and the values are explicitly bound and independent.

Validation: both delivered files compiled separately, in dependency order, with the
prescribed `scompile.py Q29 lem-trf-geometric-inverse-image-exact` invocation. The
compiler returned exit code 0 with no errors or warnings. Every universe and variable
is explicitly bound. The item record's signature and the new node's signature were
checked to be verbatim substrings of their respective modules; all Lean lines are
at most 100 characters. Delivery preflight is run through `deliver2.py --no-push`.

## Second reading by Q29

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
