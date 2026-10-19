## Worker report

The module `Sheaf.CategoryTheory.OrdinaryNerveFunctorComparison` states
`CategoryTheory.nerve.functorComparison_spec`, with one `sorry`. Its four owning
helper definitions have real data: `functorEvaluation`, `functorComparison`,
`functorPostcompose`, and `functorPrism`. The node copy changes only `lean`.
There are no new nodes, dependency repairs, statement corrections or disputed clauses.

Source read: [Kerodon Proposition the project server, Tag 0062](https://kerodon.net/tag/0062),
including its degreewise evaluation proof. The displayed comparison is the curry of
ordinary evaluation. The theorem's proof docstring reproduces all five DAG proof
steps, including the use of the fully faithful nerve from the recorded adjunction
leaf. The postcomposition and simultaneous restriction clauses are the evaluation
construction's explicit formulas, as in the node.

Clause-by-clause correspondence:

- Fixed containing universe and small ordinary categories: `universe u`,
  `(J I : Type u) [SmallCategory J] [SmallCategory I]`. All nerves and all targets
  lie in `SSet.{u}`. These are arbitrary small categories in a common containing
  universe, without finiteness, nonemptiness or groupoid assumptions.
- Ordinary functor category, natural transformations and componentwise composition:
  Mathlib's `J ⥤ I` with its existing functor-category instance; nothing is redefined.
- Evaluation on objects and mixed arrows: `evaluationUncurried J I` has object
  function `(j,F) ↦ F.obj j` and arrow function
  `(h,eta) ↦ F.map h ≫ eta.app j'`. `functorEvaluation` applies it to the pair of
  strings formed by Mathlib's `Functor.prod'`, in every simplicial degree.
- The specific comparison induced by the nerve of evaluation:
  `functorComparison J I := curry (functorEvaluation J I)`. The first conjunct is
  `IsIso (functorComparison J I)`. Thus the isomorphism concerns the actual specified
  map, and is not the existence of an unrelated isomorphism. `asIso` recovers its
  isomorphism once the first conjunct is supplied as an instance.
- String of `r` functors: `F : (nerve (J ⥤ I)) _⦋r⦌` is exactly
  `Fin (r+1) ⥤ (J ⥤ I)`. Its arrows are arbitrary natural transformations.
  In `functorPrism F`, a degree-`m` pair consists of a string `p` in `J` and
  a monotone map `a : [m] → [r]`, extracted by `SSet.stdSimplex.objEquiv`.
  Its image is `p.prod' (a.toFunctor ⋙ F) ⋙ evaluationUncurried J I`.
  In particular its objects are `t ↦ (F.obj (a t)).obj (p.obj t)`; mixed arrows
  use exactly the source arrows and natural-transformation components. This
  degreewise construction is the nerve of evaluation on `J × [r]` under the
  usual product/standard-simplex identifications.
- Every simplicial target `X`, including non-quasicategories, and every `f : N(I) → X`:
  `functorPostcompose J I f` is the actual simplicial map
  `functorComparison J I ≫ (ihom (nerve J)).map f`. The second conjunct universally
  quantifies over `X`, `f`, `r`, `F` and says its image simplex, converted by
  `SSet.yonedaEquiv.symm` and `MonoidalClosed.uncurry`, is `functorPrism F ≫ f`.
  This is equality of maps on the entire prism, not merely equality on vertices.
  Taking `X = nerve I` and `f = 𝟙 _` includes the unpostcomposed formula.
- Internal functor simplicial set for arbitrary `X`: the exact recorded internal
  hom `(ihom (nerve J)).obj X` is used. Mathlib implements it by `Functor.functorHom`;
  its degree-`n` data are natural maps from the product with the representable
  standard simplex. Currying and Yoneda supply the degreewise identification used
  explicitly in the second conjunct. Its simplicial operators precompose the
  representable parameter, exactly as in the node. No new internal-hom notion is made.
- Restriction along every `q : J' ⥤ J`: the third conjunct is an equality of
  simplicial maps, using `nerveMap ((Functor.whiskeringLeft J' J I).obj q)` on
  ordinary diagrams and `(MonoidalClosed.pre (nerveMap q)).app X` on internal homs.
- Simultaneous restriction by `q` and every monotone `a : [s] → [r]`: the fourth
  conjunct equates `(nerveMap q ⊗ₘ SSet.stdSimplex.map a) ≫ functorPrism F ≫ f`
  to the prism for the restricted string, followed by the same `f`. On the right,
  `(nerve (J ⥤ I)).map a.op F` restricts the parameter and the nerve of the
  whiskering functor restricts the source. Both operations occur in one equation.
- The stated naturality of the comparison also includes the target category:
  the last conjunct commutes the comparison with postcomposition by every ordinary
  `g : I ⥤ I'`, expressed by `Functor.whiskeringRight` and `ihom.map (nerveMap g)`.
- The particular `(k,r)` prism is the fourth conjunct with `J' = [k]` and `q` the
  chosen string; in a larger containing universe use `ULift (Fin (k+1))`.
  All monotone maps are allowed, so inner composition faces and repeated-vertex
  identity degeneracies are included. There is no invertibility or horn-filling
  hypothesis anywhere in the signature.

Dependencies and interfaces read:

- `def-cbc-enhanced-diagrams-cones`: imported publicly from
  `Sheaf.CategoryTheory.EnhancedDiagramsCones`. Its module explicitly prescribes
  using Mathlib's `SSet`, `stdSimplex`, `nerve` and `(ihom K).obj C` directly;
  its `diagramVertex`, `evaluation`, `constantDiagrams` signatures and docstrings
  were read. This item needs the simplicial primitives, not its cone constructions.
- Proof dependency `lem-coef-homotopy-category-nerve-adjunction`: its Mathlib match
  is the declaration record, with no separate Lean record required. Read
  `CategoryTheory.nerveAdjunction`, `nerveAdjunction.isIso_counit`,
  `nerveFunctorCompHoFunctorIso`, and `hoFunctor.isIso_prodComparison` in
  `Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction`; imported non-publicly
  as the proof plan requires. Also read `nerveFunctor.fullyfaithful` there.
- Mathlib's `nerve`, `nerveMap` and `ComposableArrows` signatures identify nerve
  simplices with ordinal functors. `Products.Basic` supplies `evaluationUncurried`
  and `Functor.prod'`; `Whiskering` supplies `Functor.whiskeringLeft` and
  `Functor.whiskeringRight`. `Monoidal.Closed.Basic` supplies `curry`, `uncurry`,
  `ihom`, and `pre`. `StdSimplex` supplies `stdSimplex.objEquiv` and `yonedaEquiv`.
  All were read before use; there are no private copies of these notions.

Edge cases checked before finishing:

- Empty `J`: its functor category has the unique empty functor, and both sides
  of the comparison have the unique simplex in every degree.
- Empty `I` and nonempty `J`: both sides are empty. If both are empty, both sides
  are terminal. The type-class binders do not assert nonemptiness.
- `r = 0` and `s = 0`: the formulas give the original diagram and evaluation
  along any chosen vertex. `r = 1` allows noninvertible transformations.
- For `r = 2`, the middle face composes transformations because the parameter is
  the full ordinal functor; a surjection repeats vertices and inserts identities.
- `X` is completely arbitrary, and `f` may be an identity or any other simplicial
  map. The prism formula treats these cases uniformly.
- The sole universe is an arbitrary common containing universe. No extra universe
  equation, size finiteness assumption, or missing empty case was introduced.

Searches for existing statements and constructions (2026-10-17 UTC):

- `msearch.py leanfinder`, query “The nerve of the ordinary functor category is
  isomorphic to the simplicial internal hom between nerves”: eight hits, including
  `nerveFunctorCompHoFunctorIso`, truncated full faithfulness and
  `stdSimplex.isoNerve`; none states this comparison or the parameterized formulas.
- `msearch.py leansearch`, query “nerve of functor category simplicial internal hom
  evaluation isomorphism”: eight hits, including `SimplicialNerve`, `ihom.ev`,
  `nerveFunctor`, `compEvaluation`, and `nerveFunctor.fullyfaithful`. Their source
  signatures were inspected. None is the assertion of this item.
- `msearch.py loogle`, query `CategoryTheory.nerve, CategoryTheory.Functor, SSet.ihom`:
  no hit (the last name has no `SSet` namespace). Follow-up query `"nerveMap"`:
  ten hits, individual nerve maps and truncated full-faithfulness formulas only.
- `msearch.py grep`, query
  `nerve.*(ihom|[Ee]xp|[Ff]unctor[Cc]at)|(ihom|[Ee]xp).*nerve`: no hits.
- `rg` of Mathlib's simplicial-set directory, project `lean/Sheaf`, upstream
  `WeilConjectures`, and upstream declaration index: no existing full comparison
  declaration or proposed declaration-name clash. The exact item id has no
  declaration in upstream `WeilConjectures`.
- Broader product-nerve search found `SSet.Enhanced.cartesianNervePair` and its
  degree-one specialization `cartesianNerveTransformation`, owned by
  `lem-coef-cartesian-grothendieck-colimit-formula`. They do not state this theorem.
  That owner's proof-dependency closure already reaches this item through
  enriched-diagram descent, geometric descent and augmented-vertex-cone recognition;
  importing it would make the proof-import plan cyclic. No separate pairing notion
  is introduced here: the evaluation map directly uses Mathlib's `Functor.prod'`
  and `evaluationUncurried`. The definition is the specified evaluation construction
  that this node introduces. The same Mathlib constructors define the prism.

Validation: `scompile.py Q152 lem-coef-ordinary-nerve-functor-comparison` compiled
both the sandbox file and its library-path form cleanly (about 2–3 seconds each).
All variables and universes are explicit with `set_option autoImplicit false`;
all lines are at most 100 characters. Every theorem proof is `sorry`, and the only
postponed theorem is the item's recorded statement. Independent review is performed
by the maintainer under the direct-delivery rule.

## Second reading by Q152

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
