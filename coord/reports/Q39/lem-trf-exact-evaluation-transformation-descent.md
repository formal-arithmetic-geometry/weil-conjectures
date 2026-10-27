## Worker report

States `CategoryTheory.ExactEvaluationDescent.exact_evaluation_transformation_descent`
in `Sheaf.CategoryTheory.ExactEvaluationTransformationDescent`. The original natural-language
statement, dependencies, and seven-step proof are unchanged. There is no released repair note.
The Q105 PASS is a stage-1 split review, not an existing Lean delivery; the item has no
prior `lean` record. The previous worker's stale-assignment diagnosis confused those stages.

Hypotheses and clauses are rendered as follows:

- The two abelian categories are independent `M : Type uM`, `Category.{vM} M`, `Abelian M`
  and `B : Type uB`, `Category.{vB} B`, `Abelian B`. Their derived morphism universes are
  separately `HasDerivedCategory.{wM} M` and `HasDerivedCategory.{wB} B`. The localization
  functors are Mathlib's `DerivedCategory.Q`. No universe equality is imposed.
- G and the positive-indexed H_r are `G : M ⥤ B`, `H : ℕ+ → M ⥤ M`, with Additive
  instances and explicit preservation of finite limits and finite colimits in the theorem.
  `ℕ+` is exactly r ≥ 1 and m ≥ 1; `m + 1` retains those indices.
- V and Q_r are the specified derived functors, not replacements by standard choices.
  Their CommShift and IsTriangulated instances express exactness. The isomorphisms `v`
  and `e` have exactly the displayed source and target in the node, with Lean's composition
  order reversed from the usual mathematical notation: Q_m ⋙ Q_1 means Q_1 Q_m.
- `alphaChain` composes Mathlib's `NatTrans.mapHomologicalComplex α` with the inverse
  canonical termwise-composition comparison. Its source and target are exactly C(G)
  and C(H_r) ⋙ C(G). The theorem states that its component `.f i` is α at `K.X i`.
  Its type is a natural transformation of complex functors, so its components are chain
  maps and its naturality holds for every chain map, including complexes with nonzero
  differentials. No extra chain-map or naturality assumption is introduced.
- `wordFactors` composes the given e's recursively. `evaluationFactors` composes these
  with v. At the one-letter word its hom is `V.map ((e r).hom.app K)` followed by
  `v.hom.app (C(H_r).obj K)`: the node's w_r, in Lean order. It retains every specified
  factor rather than replacing it with an unspecified standard isomorphism.
- `transformation` is the actual `Localization.liftNatTrans` construction with the two
  local Lifting records containing v and w_r. No object or map is chosen from an
  existence theorem. The unique-existence conjunct quantifies `δ : V ⟶ Q r ⋙ V` and
  gives exactly `v.hom.app K ≫ Q_B.map (alphaChain.app K) ≫ w_r.inv.app K`.
  Because δ is a NatTrans, naturality is for every arrow in D(M), including the inverse
  of any localized quasi-isomorphism. Neither α nor δ has an IsIso hypothesis.
- The second part quantifies all T_m and t_m as natural isomorphisms. Its hypothesis is
  `(t m).hom.app (Q.obj K) ≫ (e (m+1)).hom.app K =
  (Q 1).map ((e m).hom.app K) ≫ (e 1).hom.app (C(H_m).obj K) ≫
  Q.map (C(T_m).hom.app K)`, precisely the node's compatibility equation.
- Parenthesized words use Mathlib's `FreeMagma (Option ℕ+)`, with `of none` the identity.
  `EndExpression` and `EvaluationExpression` describe this node's specified generators:
  T_m and its inverse, arbitrary α for every r, identities, compositions, and all
  well-typed input/output functor images. Evaluation of an endomorphism expression
  supplies its image under G. Structural associators and unitors have both directions,
  so identities and reparenthesization do not prevent the composition of expressions.
  These constructors are notation for the finite expressions quantified by the node,
  not extra hypotheses about supplied maps or a new category of exact functors.
- Their `.chain` interpretations use the degreewise α and T and their functor images;
  their `.derived` interpretations use the actual `transformation` and specified t.
  The two normalization conjuncts state that each expression's value at QK is its
  chain-map value localized and conjugated by the recursively specified endpoint factors.
  The next two conjuncts say that any componentwise equality of chain interpretations
  gives equality of the derived natural transformations. This includes noninvertible
  α and uses the given t, not an arbitrary replacement compositor.
- The independent equality-detection conjuncts quantify all natural transformations
  between functors D(M) → D(M) and D(M) → D(B), and give equivalence between equality
  on every QK and equality of transformations. These are the two output types used here.
- A full subcategory is `S : ObjectProperty (DerivedCategory M)`. Its only hypothesis
  `hS : ∀ r X, S X → S ((Q r).obj X)` is preservation by each Q_r.
  The helper statement `word_preserves` is exactly the preservation-of-composites part
  of this clause, with an induction proof in its docstring. `restrictedWord` uses
  Mathlib's `ObjectProperty.lift`, and `EndExpression.restrict` uses `homMk` to retain
  the ambient component. Its naturality proof is the existing ambient naturality
  equation via `ObjectProperty.hom_ext`. `EvaluationExpression.restrict` is ordinary
  whiskering by S.ι. These have NatTrans types, hence naturality for every full-subcategory
  arrow. The final conjuncts preserve every chain equation under those actual restrictions.
  No stability of V, nonemptiness, repleteness, or representative in S is required.

The declarations used from the dependencies are:

- `def-sp-abelian`: `CategoryTheory.Abelian`, Mathlib.CategoryTheory.Abelian.Basic.
- `def-weil-abstract-derived-category`: `HasDerivedCategory`, `DerivedCategory`,
  `DerivedCategory.Q`, Mathlib.Algebra.Homology.DerivedCategory.Basic; complexes and
  quasi-isomorphisms are Mathlib's existing HomologicalComplex interfaces.
- `lem-weil-pbc-exact-functor-derived-factorization`: Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor,
  `CategoryTheory.Functor.mapDerivedCategory`, `mapDerivedCategoryFactors`, and its
  CommShift/IsTriangulated instances. The statement allows the specified realizations
  identified by v and e, as the node does; the imported factorization is the proof input
  ensuring that termwise exact functors invert quasi-isomorphisms after localization.
- Proof dependency `lem-weil-pbc-localization-universal-property`:
  Mathlib.CategoryTheory.Localization.Predicate, `Localization.Lifting`, `liftNatTrans`,
  `liftNatTrans_app`, `natTrans_ext`, and `fullyFaithfulWhiskeringLeft`.
- The canonical termwise maps and comparisons are `NatTrans.mapHomologicalComplex`
  and `Functor.mapHomologicalComplexCompIso` in Mathlib.Algebra.Homology.Additive.

Two named theorem proofs are postponed: `word_preserves` (the preservation assertion
needed to form the final restrictions) and the main theorem. Both belong to this
node's statement and are listed in `lean.declarations`, with source and complete proof
docstrings. All other declarations contain actual data constructed from existing
Mathlib notions. No separate independent mathematical notion or dependency repair was needed.

Edge cases checked by inspecting the typed constructions: zero/noninvertible α needs
no inverse; identity H_r and identity factors give the ordinary localized α; zero
complexes and zero differentials retain the same degreewise map; the empty word has
identity factor; structural units permit pasting an input-whiskered α after another
expression; inverse compositors use t_m.inv; arbitrary nontrivial v/e remain in the
specified order. Empty S and a zero-only stable S are permitted without assumptions;
full subcategories need not be replete. Object, arrow, and derived arrow universes
of the two abelian categories remain independent.

Searches actually run:

- msearch leanfinder: “Natural transformations of additive exact functors descend uniquely
  through specified derived factorization isomorphisms compatibly with whiskering and
  compositions”: eight hits, including `mapDerivedCategoryFactors`, Ext.mapExactFunctor_hom,
  and derived-functor fac lemmas; none states the fixed-realization composite and restriction result.
- msearch leansearch: “Natural transformations descend through specified factorizations of
  exact functors on unbounded derived categories and preserve pasting equalities”: eight
  hits about left/right derived transformations and `NatTrans.mk`, no exact match.
- msearch loogle: `CategoryTheory.NatTrans.mapDerivedCategory, CategoryTheory.Localization.liftNatTrans`:
  zero combined-query hits. `FreeMagma, Option`: zero combined-query hits. Local source
  reading independently found and used the relevant declarations, so no duplicate was made.
- msearch grep `mapDerivedCategory_app_Q_obj|mapHomologicalComplex_comp|mapHomologicalComplex_id|mapHomologicalComplex.*[Nn]at`
  in Algebra/Homology: five hits in Additive.lean, including mapHomologicalComplex_id,
  mapHomologicalComplex_comp and mapHomologicalComplex_naturality; these provide ingredients.
- msearch grep `structure.*[Rr]ealization|inductive.*[Ee]ndWord|namespace.*[Ee]valuation.*[Dd]escent`
  in CategoryTheory: zero hits. Direct rg found `FreeMagma` in Mathlib.Algebra.Free and
  `ObjectProperty.lift`/`homMk` in ObjectProperty.FullSubcategory; both are reused.
- Direct rg in both project roots for exact transformations, evaluation/descent, and
  transformation pasting found `Sheaf.CategoryTheory.ExactDerivedTransformationPasting`.
  I read the entire module. It uses its own words of arbitrary exact edges and the
  standard canonical derived comparison, not these prescribed Q_r, e_r, and compatible t_m.
  It is therefore not an exact match. The delivered syntax contains only this node's
  fixed symbols and uses the existing free-magma word type rather than duplicating that type.
- Direct rg for this node ID under WeilConjectures returned no matches. Direct rg for
  the proposed namespace and expression names in Sheaf and WeilConjectures returned no matches.

Read the source Stacks Tag 04VG (`categories.tex`, lemma-properties-left-localization),
Mathlib localization's enhancement at lines 278–365, the dependency signatures/docstrings,
and the Q105 split/report. No statement dispute or source correction was found.

Validation: scompile.py compiled the file both as sandbox and as its actual library
module in approximately 3–4 seconds per invocation. Final delivery preflight follows.

## Second reading by Q39

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
