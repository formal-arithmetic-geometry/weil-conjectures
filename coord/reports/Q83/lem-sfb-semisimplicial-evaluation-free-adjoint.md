## Worker report

The new module `Sheaf.CategoryTheory.SemisimplicialEvaluationFreeAdjoint` states
`CategoryTheory.SemisimplicialRingedTotal.semisimplicial_evaluation_free_adjoint`.
Its conclusion is a nonempty certificate `EvaluationFreeExtension` containing the
exact labelled free extension, both adjunctions, and all the specified formulas.
The certificate is an interface for this very lemma, not a second definition of
module systems or pullback. There is no choice of an arbitrary functor or map:
its inclusions, coproduct universal properties, transitions and normalized
adjunction specify the construction up to the unique compatible isomorphism.
No data definition uses `sorry`, and no `Classical.choose` is used. The sole
postponed proof is the main theorem, with the node's six-step proof in its docstring.

Clause-by-clause reading of the node:

- The index is `SemiSimplexCategory`, whose objects have length `n : ℕ` and whose
  arrows are order embeddings `Fin (n+1) ↪o Fin (m+1)`. We use its opposite because
  that is the dependency's indexing convention. Thus `p : SemiSimplexCategoryᵒᵖ`
  ranges over exactly the degrees `p ≥ 0`, and `a : m ⟶ p` labels precisely an
  injection `[p] ↪ [m]`. There is no augmented degree -1.
- All small-site, ring-sheaf, coherence and total-category data are the recorded
  dependency's `F`, `D : CoherentSitePseudofunctor ... F`, `R : RingDiagram D`,
  `h : Presheaf.IsSheaf D.totalTopology R.presheaf`, and `P : Presentation R h`.
  No new site, module category or presentation is substituted. The total module
  category is `(R.total h).modules`, and the pth module category is
  `(R.fibre p).modules`. Both use the dependency's universe `u`.
- The assumption that every transition module pullback is exact is exactly the
  theorem binder `exact`, asserting preservation of finite limits and finite
  colimits for every `(P.pullback a).ordinary`. These are additive functors by
  `Pullback.additive`. In these abelian categories this is exactness.
- The original transitions are `P.transition a`, and the original left derived
  transitions are `P.derivedTransition a`. The certificate does not posit new
  transitions on the input objects E.
- `ordinary : (R.fibre p).modules ⥤ (R.total h).modules` is the extension functor.
  Its `inclusion a` is a natural transformation from the actual pullback functor
  to `ordinary ⋙ (P.evaluation m).ordinary`. The field `coproduct` asserts
  `IsColimit (Cofan.mk ... (fun a : m ⟶ p ↦ (inclusion a).app G))` for every m,G.
  This is the displayed direct-sum formula, including its labelled inclusions,
  natural in G. An empty indexing type gives the initial object, hence zero.
- `transition` states that pullback of the a-labelled inclusion followed by the
  system's b-transition is the `(b ≫ a)`-labelled inclusion after
  `(P.composition b a).ordinary.inv.app G`. The dependency orients its composition
  comparison from the composite pullback to successive pullbacks, hence the
  inverse here. This is exactly the stipulated transition map, with no free map.
- `additive`, `limits` and `colimits` are the output functor's additivity and
  exactness. They are fields of the conclusion, not new hypotheses. The functor
  laws and the naturality of inclusions are part of the actual Lean functor and
  natural transformation structures.
- `adjunction : ordinary ⊣ (P.evaluation p).ordinary` supplies natural Hom
  bijections and both triangle identities. `homEquiv` says the bijection restricts
  a map to the identity-labelled summand, preceded by the inverse of the given
  identity-pullback comparison. `inverse_homEquiv` says on every labelled summand
  that its inverse is pullback of u followed by `P.transition a`.
- `unit` identifies the unit with the identity-labelled inclusion, using
  `(P.identity p).ordinary`. `unit_isIso` supplies the identity-summand isomorphism
  `e_p ell_p ≅ id` (the inverse of the invertible unit). The explicit `counit`
  equation says its restriction to each a summand is the original transition.
- The derived extension is literally `ordinary.mapDerivedCategory`, and derived
  evaluation is `(P.evaluation p).derived`, already defined as termwise evaluation.
  `derivedAdjunction` gives their natural bijections on the full unbounded
  derived categories. There is no boundedness, injectivity, flatness of G, or
  representability-by-a-chain-map hypothesis on the derived objects or morphisms.
- `derivedInclusion` and `derivedCoproduct` give the component direct sums with
  `(P.pullback a).derived`, the dependency's actual `Lf_a^*` functor. The fields
  `derivedTransition`, `derivedHomEquiv` and `derivedInverse_homEquiv` are exactly
  the ordinary formulas with those left derived pullbacks and derived transitions.
  In particular the inverse-adjunct formula quantifies over every derived u.
- `derivedUnit` and `derivedUnit_isIso` express the derived identity-summand
  identification. `derivedCounit` is the final clause of the node, summand by
  summand, using `P.derivedTransition a` for the given derived object E.
- The phrase “termwise functors ... induce” is retained by `inclusion_representative`,
  `unit_representative` and `counit_representative`. The first identifies the
  localized inclusion with the chain map having components `(inclusion a).app (K.X q)`.
  The latter two are precisely localization of the termwise ordinary unit and
  counit through `mapDerivedCategoryFactors`. `exactPullback` asserts that
  `(P.pullback a).alpha K` is invertible for every complex K, expressing
  `f_a^* = Lf_a^*` in the exact case with the dependency's fixed comparison, not
  an arbitrary isomorphism between the two functors.

Dependency declarations read and used:

- Statement dependency `lem-sfb-semisimplicial-ringed-total-category`:
  `Sheaf.CategoryTheory.SemisimplicialRingedTotalCategory`, namespace
  `CategoryTheory.SemisimplicialRingedTotal`; `Site.modules`, `Site.D`,
  `RingDiagram.fibre`, `RingDiagram.total`, `Presentation`, `Evaluation.derived`,
  `Pullback.ordinary`, `Pullback.derived`, `Pullback.alpha`, and the identity,
  composition and transition fields of `Presentation`. Its entire module,
  including the theorem and docstrings, was read. It is used without repair.
- Proof dependency `def-weil-sheaf-of-modules-category`:
  `Sheaf.CategoryTheory.RingedSiteModules`, `CategoryTheory.ringedSiteModules`;
  this is already the exact module-category abbreviation used by `Site.modules`.
- `def-weil-abstract-derived-category`:
  `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory` and
  `HasDerivedCategory`; the dependency fixes the standard `u+1` localization.
- `lem-weil-pbc-termwise-adjunction-homotopy`:
  `WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction`,
  `CategoryTheory.Adjunction.mapHomotopyCategory`; its termwise helper
  `Adjunction.mapHomologicalComplex` is also used in the representative formulas,
  which is why this import is public.
- `lem-weil-pbc-exact-functor-derived-factorization`:
  `Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor`,
  `CategoryTheory.Functor.mapDerivedCategory` and `mapDerivedCategoryFactors`.
- `lem-sfb-adjunction-localization`:
  `Mathlib.CategoryTheory.Localization.Adjunction`, `Adjunction.localization`,
  `localization_unit_app` and `localization_counit_app`.
- `lem-weil-pbc-exact-functor-derived-functor`:
  `Sheaf.CategoryTheory.ExactFunctorDerivedFunctor`,
  `CategoryTheory.Functor.exactFunctor_derivedFunctor`.
- `Mathlib.CategoryTheory.Limits.Shapes.Products`: `Cofan.mk` and its standard
  coproduct universal property. No duplicate sum construction is introduced.

Sources: read Stacks `spaces-simplicial.tex`, the full construction and proof of
`lemma-restriction-module-to-components-site` (0D72), exactness lemma
`lemma-exactness-g-shriek-modules` (0D74), and the statement and proof of
`lemma-derived-cartesian-shriek` (0D9E), especially part (2). As the DAG already
says, Stacks uses full Delta; the identity-only endomorphism property and the
face-only adaptation are agent-supplied. Read the current blueprint ancestor
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/`
`sk-thm-sf-ctf-stability-direct-images.proof.md`; it has no additional semisimplicial
statement replacing this auxiliary node.

Edge cases checked mathematically before finalizing the statement:

- `m < p`: there is no order embedding, so the colimit is the empty coproduct;
  its initial universal property gives the zero object. No nonempty-index
  hypothesis is imposed.
- `m = p`: the only order embedding is the identity, so the stated unit really
  is the identity-summand isomorphism. This would fail for the full simplex
  category, which is deliberately not used.
- `p = 0`, `m = 1`: the two vertex injections remain distinct labels and give
  two distinct inclusions; no uniqueness-of-face hypothesis has been added.
- Zero input: pullbacks are additive and the finite sums remain zero. Zero rings
  and empty fibre sites are allowed by the unchanged dependency interface.
- Arbitrarily unbounded complexes and morphisms represented by roofs: the derived
  objects are `Site.D`, the maps in `derivedInverse_homEquiv` are unrestricted,
  and all representatives are indexed by `ℤ`, without a lower or upper bound.
- Size: the small-site universe u and larger derived-category universe u+1 are
  the existing dependency's universes, with no new equality or smallness restriction.

Searches (all with the prescribed `msearch.py Q83 <item>` wrapper where applicable):

1. LeanFinder: “Exact left adjoint to evaluation of semisimplicial systems of
   module sheaves on varying ringed sites, given by sums of transition pullbacks”.
   Eight hits, including `SheafOfModules.PullbackConstruction.adjunction`,
   `SheafOfModules.mapFree`, and sheafification/condensed-module adjunctions.
   None is evaluation of a varying ringed semisimplicial system.
2. Loogle: `CategoryTheory.evaluationLeftAdjoint, CategoryTheory.Adjunction`.
   One hit `CategoryTheory.evaluationAdjunctionRight`, for a fixed-target functor
   category. Read its actual definition and signature: not the present statement.
3. Mathlib grep: `evaluationLeftAdjoint|evaluationAdjunction` in CategoryTheory.
   Five hits, all in `Mathlib/CategoryTheory/Adjunction/Evaluation.lean` and all
   fixed-target functor-category adjunctions, not systems of varying module categories.
4. LeanSearch: “left adjoint to evaluation for semisimplicial module sheaves,
   finite sums of pullbacks”. Eight hits, including the same fixed-target
   evaluation and unrelated ordinary pullback adjunctions. No exact match.
5. `rg` over `lean/WeilConjectures` and `lean/Sheaf` for semisimplicial evaluation,
   evaluation adjoints and free extensions; only related tower/constant-diagram
   results and the input total-category module occur. A separate literal search
   for this node id in `lean/WeilConjectures` found nothing. Final name search for
   `EvaluationFreeExtension|semisimplicial_evaluation_free_adjoint` in both library
   roots and `dag/lean_names_upstream.json` found no existing declaration.

No statement correction, disputed assertion, new DAG node, or dependency-module
repair is needed. Only the item's `lean` field changes. Its signature is copied
verbatim, including line breaks, and its declaration list includes the helper
certificate and main theorem.

Validation: prescribed `scompile.py` compiled the module in both its sandbox
and library-path checks with no messages, errors, or warnings (23.7s and 13.0s).

## Second reading by Q83

I reopened the node and the finished module and reread them clause by clause.
The explicit instruction not to start agents means this is a separate self-reading;
the delivery still receives the maintainer's independent review. I checked all
hypotheses, both Hom bijections, both directions' formulas, the component sums,
transition comparisons, identity summand, exactness and final derived counit.
The subtle orientation check is that an arrow `a : m ⟶ p` in the dependency's
opposite category corresponds to a map out of p, and that composition comparison
must be inverted in the summand transition equation. Both are correct as written.
The derived inclusions are normalized on all complexes using the actual pullback
comparison, and the derived inverse formula is for arbitrary derived morphisms,
so the statement does not merely assert an abstract derived adjunction or a
chain-map-only special case. The structure's exactness fields are conclusions;
no additional hypothesis is hidden in the theorem. No mismatch was found in
this reading, and no change to the natural-language node was made.
