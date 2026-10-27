## Worker report

The module `Sheaf.CategoryTheory.SimplexWordEvaluationDescent` states
`CategoryTheory.simplexWordEvaluation_descent`, with its proof `sorry`.
Its two real-data helper definitions belong to this node's evaluation construction:
`simplexOperatorsQuiver` sends the generators to the opposite of the supplied maps;
`simplexWordEvaluation` applies Mathlib's `Paths.lift` and unops the resulting map.
Neither introduces a second presentation, a replacement path category, or an arbitrary
choice. Both are recorded in `lean.declarations`. No new nodes, dependency repairs,
statement correction, or disputed statement are needed.

Source read: `literature/stacks-project/simplicial.tex`, Tag 0168,
`lemma-face-degeneracy-category` (b),(c), and Tag 016B,
`lemma-characterize-simplicial-object` (1)(a)--(e),(2). The proof docstring spells out
all five steps of this node: actual-word recursion; concatenation induction; the six
relation checks; the kernel congruence and its closure; quotient descent and its values.
The two adjacent mixed identities remain two separate hypotheses.

Hypothesis and clause correspondence:

- The specified presentation P is exactly `SimplexCategoryGenRel`, defined as
  `CategoryTheory.Quotient FreeSimplexQuiver.homRel`. Its words are morphisms of
  `Paths FreeSimplexQuiver`; the original `FreeSimplexQuiver.Hom.δ` and `.σ` carry
  precisely the stated finite index ranges. The quotient imposes the composition
  closure of the six relations and its equivalence closure. There is no use of
  the identification of P with Delta.
- The ordinary category is `{D : Type u} [Category.{v} D]`, with independent object
  and morphism universes. The objects are `(U : ℕ → D)`.
- Faces in degree n+1 are `d n : Fin (n + 2) → (U (n + 1) ⟶ U n)`.
  This reindexes exactly all positive source degrees of the statement, with no face
  required out of degree zero.
- Degeneracies are `s n : Fin (n + 1) → (U n ⟶ U (n + 1))`.
- The face-face assumption is `hdd`. The node's larger index is `j.succ`:
  `i ≤ j` is exactly `i < j+1`. Lean's `≫` writes the rightmost usual composite
  first, so `d (n+1) j.succ ≫ d n i` is the node's `d_i ∘ d_j`.
  The other side is `d (n+1) i.castSucc ≫ d n j`.
- The lower mixed assumption is `hds_lt`: the node's degeneracy index is `j+1`;
  `i ≤ j.castSucc` is exactly `i < j+1`.
  `s (n+1) j.succ ≫ d (n+1) i.castSucc = d n i ≫ s n j`
  is precisely `d_i ∘ s_(j+1) = s_j ∘ d_i`.
- The two adjacent mixed assumptions are respectively `hds_self` and `hds_succ`,
  `s n j ≫ d n j.castSucc = 𝟙 (U n)` and
  `s n j ≫ d n j.succ = 𝟙 (U n)`.
- The upper mixed assumption is `hds_gt`. The node's face index is `i+1`;
  `j.castSucc < i` is precisely `j+1 < i+1`.
  `s (n+1) j.castSucc ≫ d (n+1) i.succ = d n i ≫ s n j`
  is the required `d_(i+1) ∘ s_j = s_j ∘ d_i`.
- The degeneracy-degeneracy assumption is `hss`, with the same `i ≤ j`:
  `s n j ≫ s (n+1) i.castSucc = s n i ≫ s (n+1) j.succ`.
- Constancy on congruence classes is the first conjunct: for every pair of parallel
  paths, `Relation.EqvGen (@HomRel.CompClosure ... FreeSimplexQuiver.homRel a b) p q`
  implies equality of their `simplexWordEvaluation` values. This is exactly the
  quotient congruence, as confirmed by Mathlib's
  `Quotient.functor_homRel_eq_compClosure_eqvGen`.
- Descent is `∃ E : SimplexCategoryGenRelᵒᵖ ⥤ D`. The object equalities are
  `∃ h : ∀ a, E.obj (op a) = U a.len`; in particular this gives `[n] ↦ U n`.
- The next two conjuncts give the images of `(SimplexCategoryGenRel.δ i).op`
  and `(SimplexCategoryGenRel.σ i).op`, transported along `h` to be exactly
  `d n i` and `s n i`. These transports only compare morphisms in their actual
  hom types; they impose no additional assumption on D or U.
- The next conjunct explicitly identifies E on the class of every actual word,
  using `Quotient.functor FreeSimplexQuiver.homRel`, with its prescribed evaluation.
  Thus the existential functor is the descent of this evaluation.
- Reversal of composition for arbitrary presentation arrows is the next conjunct,
  `E.map (p ≫ q).op = E.map q.op ≫ E.map p.op`. In conventional composite notation
  this is exactly `E(q ∘ p) = E(p) ∘ E(q)`.
- The last conjunct states that the empty path `𝟙 a` evaluates to `𝟙 (U a.len)`.
  Together with the representative-value conjunct this is also the functor's
  empty-word value.

Dependency declarations read and used:

- The sole statement-dependency node records `simplexPresentation_faithful` in
  `WeilConjectures.CategoryTheory.SimplexPresentationFaithful`; its full theorem
  signature and docstring were read. That module is publicly imported, reusing its
  Mathlib presentation `SimplexCategoryGenRel`, its objects `mk` and `len`, and
  generators `δ` and `σ`. The faithfulness theorem itself is not a hypothesis
  or a proof dependency of word evaluation.
- Mathlib module `AlgebraicTopology.SimplexCategory.GeneratorsRelations.Basic`:
  `FreeSimplexQuiver`, its `Hom`, `homRel`, and `SimplexCategoryGenRel`.
  Each of the six `homRel` constructors was checked against the corresponding
  hypothesis. The signatures and docstrings of `toSimplexCategory` and its
  generator-value lemmas were read: they have target Delta rather than arbitrary D.
- Mathlib module `CategoryTheory.PathCategory.Basic`: `Paths.of`, `Paths.lift`,
  `Paths.lift_nil`, `Paths.lift_cons`, and `Paths.lift_toPath`. The helper evaluates
  precisely the existing free-path recursion; no new word recursion is duplicated.
- Mathlib module `CategoryTheory.Quotient`: `HomRel.CompClosure`,
  `Quotient.functor`, `Quotient.functor_homRel_eq_compClosure_eqvGen`,
  `Quotient.lift`, `Quotient.lift_spec`, and `Quotient.lift_map_functor_map`.
  The quotient construction and full lift signature were read.
- Mathlib module `CategoryTheory.Opposites`: `Functor.leftOp`, whose object and
  map definitions were read; it supplies the final orientation described in the
  proof. All these Mathlib interfaces are available through the dependency import.

Edge cases checked:

- Degree zero is included: `U 0`, `s 0 0`, and both faces from `U 1` to `U 0`
  are present; no arrow from `U 0` to a negative degree is introduced.
- Both low-degree adjacent identities give endomorphisms of `U 0`.
- `Fin.castSucc` and `Fin.succ` preserve all endpoints, including the last coface.
  The strict inequalities in the node are represented by the shifted weak bounds
  listed above, including equality at the boundary.
- Empty words are actual paths and the final clause covers every degree. All
  context words in the generated congruence can be empty.
- An empty D admits no U, as in the original statement; a terminal D satisfies
  all clauses. No nonemptiness, additivity, finite-limit or smallness restriction
  has been added. Object and hom universes are explicitly and independently bound.

Searches made with the prescribed `msearch.py Q15` item wrapper:

- LeanFinder query: "Contravariant evaluation of simplex words with faces and
  degeneracies descends to a functor on the opposite presentation category".
  Eight hits: `SimplexCategoryGenRel.toSimplexCategory`, `SSet.opFunctor`,
  `SimplexCategory.II`, `SimplicialCategory.sHomFunctor`, `SSet.stdSimplex.map_apply`,
  `SimplicialObject.opFunctor`, `SSet.stdSimplex.objMk`, and `CategoryTheory.nerve_map`.
  None constructs the arbitrary-target evaluation and descent of this node.
- Loogle query: `SimplexCategoryGenRel, CategoryTheory.Functor`.
  One hit, `SimplexCategoryGenRel.toSimplexCategory`, with target Delta.
- Mathlib grep query: `def lift|theorem lift|lemma lift|SimplexCategoryGenRel`,
  restricted to `AlgebraicTopology/SimplexCategory/GeneratorsRelations`.
  Fifteen hits in Basic, NormalForms and EpiMono: the presentation, its canonical
  Delta functor and normal-form/factorization results; no required descent theorem.
- LeanSearch query: "Construct a functor from the opposite simplex presentation
  using objects face maps and degeneracy maps satisfying simplicial identities".
  Eight hits: `CategoryTheory.SimplicialObject`, its `σ`, `δ`, `σ_def`,
  `SSet.op`, both simplicial-object/set `opFunctor`s, and `SimplexCategory.toTop`.
  These are existing simplicial objects or their operations, not the reconstruction
  from unassembled operators on the presented category.
- `rg` in `lean/WeilConjectures`, `lean/Sheaf`, Mathlib, and
  `dag/lean_names_upstream.json` for `simplexWord`, `wordEvaluation`,
  `evaluation_descent`, `evaluationQuiver`, `wordEvaluationQuiver`, and
  `simplexWordEvaluation`: no matching existing construction; unrelated
  `kunneth_evaluation_descent` in filtered tensor localization was excluded.
- `rg` for the item id in `lean/WeilConjectures` returned no declaration.
- Broader `rg` for `SimplexCategoryGenRel`, `simplexPresentation` and
  `simplicialObject_reconstruction` found the dependency module, the two Godement
  cosimplicial-existence files, and `Sheaf.CategoryTheory.SimplicialOperatorsReconstruction`.
  Their source was inspected. The Godement result is specialized and covariant;
  the reconstruction theorem returns a simplicial object on Delta and does not
  state word constancy or descent on the presentation. Neither is an exact match.

Validation: the prescribed `scompile.py` compiled the delivered file both as a
sandbox module and as `Sheaf.CategoryTheory.SimplexWordEvaluationDescent` against
the live published library, cleanly with no errors or warnings. The single theorem
has proof `sorry`; both helper definitions contain real data and no postponed proofs.

## Second reading by Q15

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
