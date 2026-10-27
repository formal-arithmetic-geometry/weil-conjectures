## Worker report

The item is stated in `Sheaf.CategoryTheory.ExpressionContextualIntertwining`, namespace
`CategoryTheory.FiniteFunctorExpressions`. Its three named sorry theorems state contextual
intertwining, invertibility of the independently specified barred map when the unbarred map
is invertible, and transport of equalities. All three are clauses of this one DAG node;
their docstrings give the corresponding proof steps. The natural-language statement is unchanged.

Hypothesis and clause correspondence:

- The node's index set I is `S : Type s`; input labels are independently `J : Type j` with
  `loc : J → S`. `C`, `D`, and `[∀ a, Category (C a)]`, `[∀ a, Category (D a)]`
  are exactly its category families. Separate C/D object and morphism universes are retained.
- The stipulated adjoint equivalence is `E : ∀ a, C a ≌ D a`. Mathlib's `Equivalence`
  has the actual forward/backward functors, specified unit/counit isomorphisms, and triangle
  law; no replacement of the given unit or counit occurs.
- The chosen typed unary and binary collections are `Operations.Unary`, `.Binary`, `.A`,
  `.B`, `.barA`, `.barB`; `.dA` and `.dB` are exactly LAR ≅ barA and LB(R-,R-) ≅ barB.
  Binary functors are honest functors on product categories, not two unrelated unary maps.
- `Expression` has input, unary and binary constructors and retains the exact parentheses.
  `Expression.evalD` and `.evalC` evaluate on the full product family categories. `reducedInputs`
  is the actual componentwise R functor. Repeated leaves are not separated or forbidden.
- `Operations.unaryComparison` and `.binaryComparison` construct a_A and a_B by the inverse
  of the image of the specified counit followed by the given d component. Composition in
  Lean is diagrammatic, reversing the order of the node's right-to-left notation.
- `Expression.comparison` recursively constructs precisely c_i = u_i⁻¹, then a_A followed
  by barA(c), or a_B followed by barB(c,c). `.coefficientComparison` is R(c⁻¹) followed
  by e, exactly r_V. These are real isomorphism constructions with no sorry or choice.
  Using the recursively constructed c realizes any c satisfying the node's recursion,
  since the recursion fixes c uniquely on each finite syntax tree.
- `Paired.generator` takes independent natural transformations h and k on the whole
  D-input and C-input categories. Its sole equation, for every K, is r_V ≫ h_(RK) =
  R(k_K) ≫ r_T. No h invertibility, evaluation faithfulness, or component-arrow lifting is assumed.
- `expression_contextual_intertwining` says L(h_(RK)) ≫ c_T = c_V ≫ k_K for any
  generated pair. Instantiating `Paired.generator h k coefficient` is the generator implication.
  The constructors `unary`, `binary`, `identity`, `comp`, and `inverse` give exactly all
  requested closure operations. One changed binary slot uses `identity` in the other; two
  changed slots use both pairs. A repeated hole uses the same pair in multiple children.
  Thus inductively inserting the generator into any finite outer context gives the displayed
  context equation using that context's actual recursively constructed comparisons.
- The inverse constructor accepts both isomorphisms; `expression_contextual_intertwining_isIso`
  supplies barred invertibility whenever unbarred invertibility is given, so this excludes
  no allowed inverse. `asIso` then permits the inverse constructor.
- `expression_contextual_intertwining_eq` quantifies over two derivations with the same
  endpoints and assumes equality h = h' as natural transformations; its conclusion is k = k'.
  This states transport of equalities between arbitrary composites and contexts, using the
  same endpoint c on both routes. Barred maps are never defined by conjugation.
- The allowed full-subcategory restrictions are covered by taking C and D to be those
  categories with the restricted E and operation data. The theorem imposes no ambient
  category or global closure beyond existence of the stated functors and comparisons.

Dependency declaration: `def-nagata-category` is the Mathlib leaf
`CategoryTheory.Category`, `Mathlib.CategoryTheory.Category.Basic`; read its full
CategoryStruct data and Category laws. The new definition node supplies the generic syntax
not present in that leaf. Mathlib declarations reused are `CategoryTheory.Equivalence`
(`Mathlib.CategoryTheory.Equivalence`), `Pi.eval` and `Functor.pi`
(`Mathlib.CategoryTheory.Pi.Basic`), `Functor.prod`, `Functor.prod'`, `NatTrans.prod'`,
`Iso.prod` (`Mathlib.CategoryTheory.Products.Basic`), `Functor.mapIso`, and
`Functor.whiskerRight` (`Mathlib.CategoryTheory.Whiskering`). Their source signatures
were inspected. The only proof dependency is the same category leaf, already publicly available.

Edge cases checked before writing: empty S, empty input set and operation collections,
empty categories, identity-only syntax, arbitrary noninvertible generator, repeated input
and repeated hole, change in either/both binary slots, and inverse/composite routes.
No finite or nonempty typeclass is imposed on inputs or symbols. The expression inductive
itself ensures finiteness. All universes and variables are explicitly bound; the symbol
universe is explicitly passed to Operations to avoid accidental specialization.
A vector-space sanity check with nontrivial scalar unit/counit confirms the orientation
of c and r and cancellation. No statement dispute or correction was needed.

Searches (all remote searches logged by msearch.py): LeanFinder's adjoint-equivalence/context
query returned CommSq and CatCommSq mate results, with no recursive-expression theorem.
Its finite typed unary/binary expression query returned polynomial-functor W-types, not
this syntax. LeanSearch's finite typed expression query returned evaluation adjunctions
and exponential comparisons. Loogle `CategoryTheory.NatTrans, CategoryTheory.Functor.prod`
returned zero hits. Mathlib grep `TypedExpression|ExpressionContext|contextual|conjugateEquiv_whisker`
found generic mates/whiskering declarations, not the item. Grep
`inductive.*(Expression|Context)|TypedExpression` in CategoryTheory returned zero hits.
Read the relevant mate signatures; they do not supply the independently specified recursive c.
Project searches over WeilConjectures, Sheaf, and dag/lean_names_upstream.json for
TypedExpression, ExpressionContext, contextual and intertwining found no duplicate.
The upstream node-id grep found no declaration. DAG searches identified only geometric
integral-system expressions and completed tensor/pullback expressions; their constructors,
categories and interfaces specialize to schemes, so they cannot represent arbitrary
category families and arbitrary typed symbols. Blueprint searches for `typed expression`
and `functor expressions` both returned zero. The new node records the actual search-log
records, including query, service result names and digests.

Validation: both delivered files compile separately in dependency order with scompile.py;
no errors or warnings. The sole postponed proofs are the three named clauses of the item.

## New nodes

`def-sf-finite-functor-expressions` introduces the generic Operations/Expression/Paired
interface and its exact recursive evaluations, c, and r in
`Sheaf.CategoryTheory.FiniteFunctorExpressions`. Its source is the coefficient-comparison
and inherited-equations sentences of fix-prop-coherence.proof.md, expanded explicitly in
this item's statement and proof steps 1--11. Its only dependency is the category leaf.
All data is constructed in full. The searches above distinguish it from scheme-specific
completed operations and integral-system syntax and from Mathlib's unrelated W-types.
It is cited in the item's stmt_deps; no existing dependency record was replaced.

## Second reading by Q112

No separate worker reading was performed: the dispatch brief forbids starting other agents
and specifies direct delivery followed by the maintainer's independent review. The detailed
clause mapping above is the author's own reading, not an independent review.
