## Worker report

The module `Sheaf.CategoryTheory.DerivedCategory.AugmentedCopowerDerivedCounit`
states the item in four public theorems, all with proof `by sorry`:
`CategoryTheory.augmentedCopower_transpose_formula`,
`CategoryTheory.augmentedCopower_derived_counit`,
`CategoryTheory.augmentedCopower_evaluated_counit`, and
`CategoryTheory.augmentedCopower_transpose_naturality`.
There are no definitions, instances, new nodes, dependency repairs, statement
corrections, or disputed statements in this delivery. The node is changed only
in `lean`.

Sources actually read: `literature/stacks-project/sites-cohomology.tex`,
`example-morphism-categories` (Tag 08PH), including its chaotic-topology,
constant-coefficient and generator-map conventions; and
`literature/stacks-project/derived.tex`,
`lemma-pre-derived-adjoint-functors-general` and
`lemma-pre-derived-adjoint-functors` (Tag 0DVC), including the six Hom
identifications and their functoriality. The item's five proof steps supply the
arbitrary-coefficient augmented-resolution specialization of those sources.

Hypothesis-by-hypothesis and clause-by-clause correspondence:

1. Small categories and the functor are `{E D : Type u}`, `[SmallCategory E]`,
   `[SmallCategory D]` and `(u : E ⥤ D)`. The common universe is the small-site
   bound already used by the representable-module dependency. Derived Hom sizes
   remain independent universes `wE`, `wD`, and `wR`. There is no bound on the
   number of objects or generators beyond smallness in this bound.
2. The identity-cover topology imposes no extra condition on presheaves. Thus
   the node's explicitly named category `A_C = Fun(Cᵒᵖ, Mod_R)` is represented
   literally as `Cᵒᵖ ⥤ ModuleCat.{u} R`. The source convention is not replaced by
   an arbitrary ringed site or by presheaves with a further sheaf hypothesis.
   `[CommRing R]` is the stated coefficient-ring hypothesis.
3. Exact precomposition is the existing
   `(Functor.whiskeringLeft Eᵒᵖ Dᵒᵖ (ModuleCat.{u} R)).obj u.op`.
   Its ordinary left adjoint is `u.op.lan`, with the actual
   `u.op.lanAdjunction (ModuleCat.{u} R)`; these are not arbitrary adjoint
   functors or maps. Complexes are `CochainComplex ... ℤ` and termwise action
   is `mapHomologicalComplex (ComplexShape.up ℤ)`.
4. `K : Dᵒᵖ ⥤ ModuleCat.{u} R` and the existing
   `HomologicalComplex.single ... (ComplexShape.up ℤ) 0` give `K[0]`.
   `α` has target the termwise restriction of precisely this complex.
   `[QuasiIso α]` is the augmentation quasi-isomorphism. The named
   `singleObjXSelf` isomorphism identifies its term in degree zero with K;
   this avoids silently treating a transported zero-degree object as literal K.
5. `hC : ∀ r : ℤ, 0 < r → IsZero (C.X r)` is the positive-degree vanishing.
   `J : Type u`, `U : J → E`, `M : J → ModuleCat.{u} R`, and the specified
   `d : C.X 0 ≅ ∐ ...` give exactly the specified decomposition. Its summands
   are the dependency's existing `evaluationLeftAdjoint ... (op (U j))`.
   No projectivity or freeness of the coefficient modules is assumed.
6. `f` together with `hf` renders the node's defining sentence for `f_j`:
   the inner `Sigma.ι` is the identity-arrow inclusion, the outer `Sigma.ι`
   includes the jth copower, `d.inv` enters C⁰, and `α.f 0`, followed by the
   degree-zero single-complex isomorphism, maps to `K(uU_j)`. Thus `hf` fixes
   f uniquely from the given data; it does not impose an additional condition
   on the augmentation. The first conjunct of `transpose_formula` states the
   required formula for α at every arrow `t : op (U j) ⟶ W`.
7. The binder `c` with `hc` identifies c with the ordinary adjunct under the
   actual Kan adjunction on complexes. This is the node's definition of c,
   not a hypothesis that an unrelated map has the required formula.
8. The existential isomorphism `e` in `transpose_formula` identifies
   `u.op.lan.obj (C.X 0)` with the sum of copowers at `u.obj (U j)`.
   Its first conjunct is the dependency's unit normalization, transported by
   the specified decomposition d. Hence it is the canonical Kan coordinate
   map. Its second conjunct is the equation on each target copower inclusion:
   inclusion followed by `e.inv`, `c.f 0` and the zero-degree single-complex
   identification equals `f j ≫ K.map t`. Evaluating this equality of linear
   maps on any x is exactly `c⁰_V(j,t,x) = K(t)f_j(x)`.
9. The next conjunct is `∀ r, r ≠ 0 → c.f r = 0`, so c is zero in every
   degree other than zero. The following conjunct is
   `u.op.lan.map (C.d (-1) 0) ≫ c.f 0 = 0`, the stated annihilation of the
   incoming differential, including its actual Kan image.
10. The final conjunct of `transpose_formula` is naturality for every
    restriction arrow and every degree r. In the opposite category the arrow
    `s : V ⟶ V'` represents `V'.unop ⟶ V.unop`, so it says exactly
    `K(s)c_V = c_V'(g_!C)(s)`, with the necessary single-complex term
    identification in degree zero. The final theorem also spells out the
    generator restriction identity `f j ≫ K.map (t ≫ s) =
    f j ≫ K.map t ≫ K.map s`.
11. The derived statements bind `L`, its comparison `ε`, and `hL`, the actual
    total-left-derived universal property at the quasi-isomorphisms.
    They take the everywhere-defined derived functor supplied by the cited
    dependency as data; they do not assert its existence again. Its everywhere
    definedness and triangulatedness are supplied there and are not additional
    conditions needed by the equations here. `[IsIso (ε.app C)]` is exactly
    the acyclicity/computation hypothesis of this node.
12. The adjunction `a : L ⊣ restriction.mapDerivedCategory` is constrained by
    `hnorm` for every complex X, N, and every ordinary chain map b. This is
    verbatim the normalized Hom-bijection condition from
    `ContinuousCocontinuousDerivedShriekData.normalization`, in the presheaf
    presentation. In particular a is not an unconstrained derived adjunction.
    Its `a.counit.app (DerivedCategory.Q.obj (K[0]))` is the node's e_K.
13. `augmentedCopower_derived_counit` states both displayed identities as two
    conjuncts. Because `mapDerivedCategory` is identified with termwise action
    by a canonical isomorphism, `Q.map α` is followed by
    `restriction.mapDerivedCategoryFactors.inv.app (K[0])` before applying L.
    The first equality is `LQ(α) ≫ e_K = ε_C ≫ Q(c)`; the second is
    `e_K = inv (LQ(α)) ≫ ε_C ≫ Q(c)`. Lean's composition order is opposite
    the usual written function-composition order. Localization inverts α,
    the factorization is an isomorphism, and functors preserve isomorphisms;
    no additional invertibility hypothesis on LQ(α) is introduced.
14. `augmentedCopower_evaluated_counit` applies the exact evaluation functor's
    `mapDerivedCategory` to the actual counit. The right side is the evaluated
    source identification, followed by its canonical factorization, then
    `DerivedCategory.Q.map (evaluation.mapHomologicalComplex.map c)`, and the
    inverse target factorization. Thus the representative at each V is the
    localization of exactly the displayed c_V. There is no arbitrary
    representative or abstract existence assertion in place of this equality.
15. The last theorem quantifies K', C', α', q, v, c' and their defining adjunct
    equations. Its hypothesis h is exactly the augmentation square
    `v ≫ α' = α ≫ restriction(q[0])`. Its first conjunct is the ordinary
    equality `c ≫ q[0] = g_!(v) ≫ c'`; its second is the localized equality
    after the canonical comparisons `ε_C` and `ε_C'`. These are precisely the
    derived representatives in the preceding theorem. No preservation of
    either chosen decomposition by v is imposed. The uninverted naturality
    equation does not need an invertible comparison or augmentation at C'.
16. The last conjunct states coefficient naturality as equality of linear
    maps `f j ≫ K.map t ≫ q.app V =
    f j ≫ q.app (op (u.obj (U j))) ≫ K'.map t`. On any element x this is
    exactly the final displayed formula in the node.

The four statements separate clauses according to the data used by each: for
example naturality applies without an acyclicity hypothesis, and the two counit
identities need no chosen decomposition. Applying all four to the data of the
node gives every clause with the same objects and maps. No clause is replaced
by a theorem about different coefficients or an arbitrary Kan-coordinate map.

Dependency declarations read and used:

- `def-weil-size-convention`: its convention-only record has no Lean
  declaration; explicit universe polymorphism and `HasDerivedCategory` render it.
- `Sheaf.CategoryTheory.SiteCoveringAxioms`,
  `CategoryTheory.Precoverage.IsSiteForCoverings`: read its complete definition
  and docstring. Identity coverings yield the ordinary presheaf category, as
  explicitly stipulated in this item and in the representable dependency.
  No new covering notion is introduced here.
- `Sheaf.CategoryTheory.RingedSiteModules`,
  `CategoryTheory.ringedSiteModules`: read its complete abbreviation and
  docstring; here the node itself identifies those modules with the functor
  category for a constant ring and identity covers.
- `Mathlib.Algebra.Homology.DerivedCategory.Basic`, `DerivedCategory`,
  `HasDerivedCategory`, and `DerivedCategory.Q`: the recorded derived
  localization, retaining independent chosen Hom universes.
- `Sheaf.CategoryTheory.ContinuousCocontinuousDerivedShriek`,
  `CategoryTheory.ContinuousCocontinuousDerivedShriekData` and
  `CategoryTheory.continuousCocontinuous_exists_derivedShriek`: read the full
  signatures and all fields, especially comparison, universal property,
  derivedAdjunction, and normalization. Their presheaf specialization is the
  data used by the two counit statements. No alternative derived functor or
  alternative normalization is defined.
- `Sheaf.CategoryTheory.DerivedCategory.RepresentableSumShriekAcyclic`,
  `CategoryTheory.representableModule_formulas`,
  `CategoryTheory.representableModule_colim_lan`, and
  `CategoryTheory.representableModule_sum_lan_acyclic`: read the coefficient
  copower signatures, the normalized Kan-coordinate condition and docstrings.
  The statement uses precisely their Mathlib constructions
  `evaluationLeftAdjoint`, `Sigma.ι`, `u.op.lan`, and `u.op.lanAdjunction`.
  Its additive instances enable termwise action on complexes.

Searches actually run:

- `msearch.py leansearch`, query `counit derived adjunction augmented resolution
  representable presheaf`: eight hits, including `Adjunction.counit`,
  `Adjunction.derivedε`, and `Adjunction.derived_counit`. No combined statement.
- `msearch.py leanfinder`, query `Ordinary transpose of augmented copower
  resolution represents normalized derived adjunction counit`: eight generic
  derived-adjunction hits, including `Adjunction.derived_counit` and
  `Adjunction.derivedε_fac_app`. No copower-resolution statement.
- `msearch.py loogle`, query `CategoryTheory.Adjunction.derived_counit,
  CategoryTheory.evaluationLeftAdjoint`: zero hits.
- `msearch.py grep`, query `derived_counit|lanAdjunction_counit_app` in
  `CategoryTheory`: five hits in KanExtension/Adjunction.lean, concerning the
  ordinary counit, without the augmented resolution formula.
- Direct `rg` of `lean/WeilConjectures`, `lean/Sheaf`, and
  `dag/lean_names_upstream.json` for `augmented.copower`, `copower.*counit`,
  `augmentedCopower`: no existing match. Broader `copower|derived_counit|
  augmented.*[Cc]ounit` found the representable dependency and generic derived
  infrastructure, not this statement. A direct node-id grep in
  `lean/WeilConjectures` had no hits. All four new declaration names had no
  upstream occurrence before the module was written.
- Read the relevant Mathlib source declarations in
  CategoryTheory/Adjunction/Evaluation.lean,
  CategoryTheory/Functor/KanExtension/Adjunction.lean,
  CategoryTheory/Functor/Derived/Adjunction.lean,
  Algebra/Homology/Single.lean, and
  Algebra/Homology/DerivedCategory/ExactFunctor.lean. These supply the exact
  existing constructions, but none states the combination of clauses here.

Edge cases checked against the signatures and the proof:

- Empty E, D when a functor exists, and empty J are allowed. Empty coproducts
  are zero and generator equations are vacuous; vanishing and counit equations
  still refer to the actual zero maps. No `Nonempty` premise is added.
- Zero ring, zero modules and zero K are included. No nontriviality, flatness,
  freeness or projectivity of M is used.
- C may extend arbitrarily far to the left; there is no bounded-below or
  finite-resolution condition. Negative degrees are all covered by the
  `r ≠ 0` vanishing assertion, and degree -1 is explicit in the chain equation.
- Identity functors and identity restriction arrows are included. The unit
  normalization gives the identity coefficients in these cases, and the
  comparison factors retain the actual normalized counit.
- v is any chain map satisfying the augmentation square, including zero
  coefficient maps and maps mixing the chosen summands.
- The distinct derived Hom universes are never equated, including the universe
  for evaluated module complexes. All variables and universes are explicit;
  `set_option autoImplicit false` is present.

Validation: the prescribed `scompile.py` compiled the delivered file in both
sandbox module mode (6.7 s) and its actual library module mode (5.4 s), with no
errors or unexpected warnings. Every theorem has only `sorry` as proof; each
has the source, blueprint identifier, and its corresponding complete proof
steps in the docstring. No global build or live source modification was run.

## Second reading by Q48

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
