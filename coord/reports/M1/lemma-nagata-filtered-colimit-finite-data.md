## Worker report

The module `Sheaf.RingTheory.FilteredColimitFiniteData` states
`CommRingCat.exists_finite_data_stage`; its only proof is `sorry`.
No new notions, dependency modules, or statement corrections are needed.
The source blueprint was read over SSH on the server at
`literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-approximation/lemma-nagata-filtered-colimit-finite-data.md`.
The stage-1 node makes explicit the commutativity and nonemptiness needed by its proof.

Hypothesis and clause correspondence:

- The nonempty directed set is `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`. A preorder is the project's required directed-set encoding;
  it permits equivalent distinct indices and has one categorical arrow for each inequality.
- The compatible system of commutative rings and ring maps is
  `(F : I ⥤ CommRingCat.{u})`. Functor identity and composition laws express the
  compatibility. The preorder category is supplied by Mathlib.
- The colimit ring A is `CategoryTheory.Limits.colimit F`, using the dependency's
  recorded chosen categorical colimit, rather than a separately defined direct limit.
  Mathlib's `Ring.Colimits` supplies existence automatically for this small diagram,
  so there is no redundant `HasColimit F` hypothesis. The index and rings share universe u.
- Finitely many elements are `(n : ℕ)` and `(x : Fin n → ↑(CategoryTheory.Limits.colimit F))`.
  Finite lists allow repetitions and the empty selection. Every finite selection admits
  this enumeration, so this does not exclude finite sets of elements.
- Finitely many pairs of ring expressions are `(m : ℕ)` and
  `(p q : Fin m → MvPolynomial (Fin n) ℤ)`.
  Every expression formed from the selected elements, 0, 1, addition, subtraction,
  negation, and multiplication is an integer polynomial in those elements, and every
  such polynomial is a ring expression. Commutativity makes this representation exact;
  it imposes no polynomial degree bound. Constants from A, if present in an expression,
  are additional selected elements, as in the source's finite-data argument.
- The assumed equalities in A are `h : ∀ r : Fin m,
  (p r).eval₂ (Int.castRingHom ↑(CategoryTheory.Limits.colimit F)) x =
  (q r).eval₂ (Int.castRingHom ↑(CategoryTheory.Limits.colimit F)) x`.
- One stage and simultaneous lifts are `∃ (i : I) (y : Fin n → F.obj i)`
  and the first conjunct `∀ a, colimit.ι F i (y a) = x a`.
- All selected equalities hold there: the second conjunct evaluates each `p r` and
  `q r` using `Int.castRingHom (F.obj i)` and the same `y`.
- They persist under every later transition: the third conjunct quantifies over
  `(j : I) (hij : i ≤ j) (r : Fin m)` and evaluates both polynomials on
  `fun a ↦ F.map (homOfLE hij) (y a)` in `F.obj j`.

Dependency declarations read and used: `def-weil-pbc-category-colimit` records
`CategoryTheory.Limits.colimit` in `Mathlib.CategoryTheory.Limits.HasLimits`.
Its full definition, coprojection signature and docstrings were read, together with
`Cocone` and `IsColimit` (Cones and IsLimit). The module uses the recorded colimit
and its `CategoryTheory.Limits.colimit.ι` coprojections through Ring.Colimits.
Other existing notions used are `MvPolynomial.eval₂` (Algebra.MvPolynomial.Eval),
`Int.castRingHom` (Data.Int.Cast.Lemmas), and `homOfLE` (CategoryTheory.Category.Preorder).
These existing Mathlib notions need no additional definition nodes. The complete
five-step natural-language proof in the theorem docstring follows the node's one
proof paragraph and names both proof dependencies.

Edge cases checked before writing:

- `n = 0`: the lift is the unique empty family; even integer-only equalities that
  become true in the colimit can be enforced at a stage by eventual equality.
- `m = 0`: there are no equality obligations; the conclusion is simultaneous lifting.
- `n = m = 0`: nonemptiness supplies a stage. Thus nonemptiness cannot be omitted.
- Zero rings and arbitrary characteristics are allowed: no Nontrivial or characteristic
  assumption occurs, and integer evaluation works in every commutative ring.
- The constant single-stage diagram gives the original equalities unchanged.
- Infinite directed preorders, non-injective transition maps and repeated selected
  elements are all allowed; equality need only become true after a transition.
- Index universe u matches CommRingCat.{u}, following the current index-universe rule.

Searches made (complete service records are in the sandbox's searches.jsonl):

- LeanFinder: `finite elements and finite polynomial equalities lift to a common stage
  of a directed colimit of commutative rings` returned eight hits, including
  `Ring.DirectLimit.Polynomial.exists_of` and
  `RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`. These concern polynomial
  coefficient lifting or morphisms from finitely presented rings, not this exact
  simultaneous finite-elements/equations/persistence statement.
- Loogle: `MvPolynomial.eval, CategoryTheory.Limits.IsColimit` returned zero hits.
- LeanSearch: `finite elements and equalities in filtered colimit rings lift to one
  stage` was unavailable with Internal Server Error. No verdict is inferred from it.
- msearch grep: `finite.*(equation|relation)|exists.*(lift|rep)|isColimit_rep_eq`
  in `Algebra/Category/Ring` returned only the unrelated small-representative result
  in `Mathlib/Algebra/Category/Ring/Small.lean`.
- Local rg: `finite_data|finiteData|lemma-nagata-filtered-colimit-finite-data` in
  `WeilConjectures` and `lean/Sheaf` returned only the unrelated etale finite-data
  descent theorem. Additional `filtered.*colimit|finite.*equalit|finite.*data`
  searches of the ring-theory directories found other colimit applications, not
  an exact match. The blueprint id has no source declaration.
- Mathlib Eval source search found `MvPolynomial.eval₂` and `map_eval₂`, confirming
  that polynomial evaluation and its compatibility with ring maps already exist.

Validation: server compilation and deliver2 dry run are run before reporting READY.
No statement dispute or node fault was found.

## Second reading by M1

I opened the stage-1 node, its recorded dependency, the source blueprint reference in
`literature/blueprint/master/blueprint/sec-nagata-compactification/sk-prop-nagata-sketch-approximation/lemma-nagata-filtered-colimit-finite-data.md`, and the Lean module.
The item-by-item correspondence is:

- The node's nonempty directed set is rendered by `{I : Type u} [Preorder I] [Nonempty I]
  [IsDirected I (· ≤ ·)]`; no stronger order or finiteness assumption is added.
- The directed commutative-ring system is `F : I ⥤ CommRingCat.{u}`. Its functor laws
  provide exactly the compatible ring maps indexed by the preorder.
- The colimit object is `CategoryTheory.Limits.colimit F`, with coprojection
  `colimit.ι F i`; this uses the dependency's Mathlib declaration and the standard
  filtered colimits of commutative rings, without a redundant `HasColimit` hypothesis.
- The finite selected data are `n m : ℕ`, `x : Fin n → ↑(colimit F)`, and
  `p q : Fin m → MvPolynomial (Fin n) ℤ`. Integer multivariate polynomials encode all
  commutative-ring expressions in the selected elements, including constants and the
  empty family.
- The input equalities are exactly `h : ∀ r : Fin m, (p r).eval₂
  (Int.castRingHom ↑(colimit F)) x = (q r).eval₂
  (Int.castRingHom ↑(colimit F)) x`.
- The conclusion first gives one stage and simultaneous lifts,
  `∃ (i : I) (y : Fin n → F.obj i)`, with
  `∀ a, colimit.ι F i (y a) = x a`.
- Its second clause requires every selected polynomial equality at stage `i`, using
  `Int.castRingHom (F.obj i)` and `y`.
- Its third clause requires those equalities at every `j` with `hij : i ≤ j`, after
  applying `F.map (homOfLE hij)` to every lift. The quantifier order and all clauses
  match the node.

No mismatch was found, so no Lean statement or definition was changed. The only delivery
change is recording the compiled declaration in the node's `lean` field. Edge cases checked
are `n = 0`, `m = 0`, and `n = m = 0`; `Nonempty I` supplies a stage. Zero rings,
arbitrary characteristics, repeated elements, non-injective transitions, and infinite
preorders remain allowed. The universe is shared (`I : Type u`, `CommRingCat.{u}`), so no
covered case is excluded.

Searches found no exact existing statement or definition. LeanFinder and Loogle searches
returned only generic filtered-colimit, finite-presentation, or polynomial-evaluation
results; LeanSearch was unavailable; grep searches of Mathlib, `WeilConjectures`, and
`lean/Sheaf` found no exact finite-data theorem. The only notion dependency is the
recorded Mathlib `CategoryTheory.Limits.colimit` (with `colimit.ι`, `Cocone`,
`IsColimit`, and `CategoryTheory.IsFiltered`), which was used directly. Compilation with
`scompile.py` succeeds with only the theorem's permitted `sorry`.
