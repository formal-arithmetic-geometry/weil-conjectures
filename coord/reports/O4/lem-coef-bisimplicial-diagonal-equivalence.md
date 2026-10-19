## Worker report

The module `Sheaf.AlgebraicTopology.BisimplicialDiagonalEquivalence` states
`SSet.bisimplicial_diagonal_equivalence` with its whole proof `by sorry`.
It also constructs `SSet.bisimplicialZerothRowIndex`, the canonical index
transformation needed to specify the final map. It has actual morphism data and
proved naturality; it chooses no maps or objects from existence assumptions.
There are no new nodes, dependency modules, statement changes, or disputed statements.
Only the item's `lean` field changes.

Clause-by-clause correspondence:

- A bisimplicial set is literally
  `SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ ⥤ Type u`, and a morphism is `f : D ⟶ E`,
  hence a natural transformation. The universe `u` is arbitrary and explicitly bound.
- Its diagonal is `Functor.diag SimplexCategoryᵒᵖ ⋙ D`, whose value at `n` is
  `D.obj (n,n)` and whose operator at `a` is `D.map (a ×ₘ a)`.
  The induced map is `whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) f`.
- The first conjunct quantifies over every `D`, `E`, and `f`. Its hypothesis
  `∀ m : ℕ, Enhanced.IsWeakHomotopyEquivalence
  (whiskerLeft (Prod.sectR (Opposite.op ⦋m⦌) SimplexCategoryᵒᵖ) f)`
  is exactly weak equivalence on every row `D_{m,•} → E_{m,•}`.
  Its conclusion is the stated weak equivalence of diagonals.
- The second conjunct has the same quantifiers and conclusion. It uses
  `Prod.sectL SimplexCategoryᵒᵖ (Opposite.op ⦋n⦌)` for every `n : ℕ`, exactly
  the exchanged-direction, columnwise hypothesis.
- The third conjunct quantifies over every `D`. The condition
  `∀ (m n : SimplexCategoryᵒᵖ) (a : m ⟶ n),
  Enhanced.IsWeakHomotopyEquivalence ((curry.obj D).map a)` means that every
  structure map of the horizontal simplicial diagram is a weak equivalence.
  This includes arbitrary simplicial operators, not merely faces or degeneracies.
- `bisimplicialZerothRowIndex` is a transformation from
  `Prod.sectR (Opposite.op ⦋0⦌) SimplexCategoryᵒᵖ` to
  `Functor.diag SimplexCategoryᵒᵖ`. At `n` it is
  `(SimplexCategory.const n.unop ⦋0⦌ 0).op ×ₘ 𝟙 n`.
  Thus `whiskerRight bisimplicialZerothRowIndex D` has source the actual zeroth
  row and target the actual diagonal, with component
  `D.map (([n] → [0])ᵒᵖ, 1)`. This is precisely the diagonal of the comparison
  from the constant diagram on that row. It is not an arbitrary weak equivalence
  or an unspecified isomorphism. The final conclusion asserts weak equivalence
  of this particular map.
- All appearances of weak homotopy equivalence are the dependency's
  `SSet.Enhanced.IsWeakHomotopyEquivalence`: bijectivity of realized path
  components and of all positive based homotopy groups at every basepoint.
  There is no Kan-complex, fibrancy, connectedness, nonemptiness, or finiteness
  assumption in any clause.

Dependencies read and used:

- `def-weil-pbc-simplicial-set` is a Mathlib leaf. Read the signatures and
  docstrings for `SSet` in `Mathlib.AlgebraicTopology.SimplicialSet.Basic`,
  `SSet.degenerate`/`SSet.nonDegenerate` in `...Degenerate`,
  `SSet.Subcomplex` in `...Subcomplex`, and `SSet.Finite` in `...Finite`.
  This item uses the functor-category definition `SSet`; it does not need the
  finiteness or subcomplex clauses. No dependency is redefined.
- `Sheaf.AlgebraicTopology.KanQuillenRightProper`,
  `SSet.KanQuillen.right_proper_kan_quillen` and its
  `SSet.KanQuillen.weakEquivalenceStructure` were read in full. That structure
  fixes its weak equivalences to `SSet.Enhanced.IsWeakHomotopyEquivalence`,
  read in `Sheaf.CategoryTheory.EnhancedDiagramsCones`. The existing predicate
  is used directly; no alternate weak-equivalence structure is introduced.
- For the proof plan the file imports the stated dependency
  `Sheaf.CategoryTheory.ReedyModelStructure`,
  `HomotopicalAlgebra.Reedy.model_structure`, read with its docstring and signature.
- Proof-dependency Mathlib imports are `...ModelCategory.BrownLemma`
  (`CofibrantBrownFactorization`, its nonempty instance and split section),
  `...SimplicialSet.AnodyneExtensions.PushoutProduct`
  (`SSet.anodyneExtensions_pushoutObjObjι`), and `...SimplicialSet.Degenerate`
  (`SSet.exists_nonDegenerate`, `unique_nonDegenerate_dim`,
  `unique_nonDegenerate_simplex`, `unique_nonDegenerate_map`). These declarations
  and their recorded matching signatures were read. They are private imports
  because they are used by the future proof only.
- Mathlib's `Functor.diag`, `Prod.sectR`, `Prod.sectL`, `Functor.curry`,
  and both whiskerings supply all categorical constructions. The helper merely
  supplies the canonical natural transformation between these existing functors.

Source: opened the original Cisinski PDF at
`https://cisinski.app.uni-regensburg.de/CatLR.pdf` and checked Theorem 3.1.16,
printed pp. 79--81. Its levelwise diagonal assertion agrees with this statement;
exchanging variables and the constant-row specialization are explicit in the
DAG's proof steps 5 and 6. The theorem docstring carries all six DAG proof steps,
including degree-zero latching objects, the relative skeletal attachment,
its diagonal pushout product, Brown split factorization, the transpose, and the
specified constant-row comparison.

Edge cases checked: degree zero is included by both `ℕ` quantifiers; at zero
the unique map `[0] → [0]` is the identity, so the canonical component is the
identity. Empty bisimplicial sets are allowed, and no vertex/basepoint is
required to exist. Arbitrary disconnected or non-Kan rows and columns are
allowed. Both directions use the same diagonal and the same induced map.
No universe equality or smallness assumption on the sets is imposed.

Searches made with `msearch.py`:

- LeanFinder: “Taking the diagonal of a rowwise weak homotopy equivalence of
  bisimplicial sets preserves weak homotopy equivalences”. Eight hits, all general
  model-category weak-equivalence or homotopy lemmas; no exact statement.
- Loogle: `SSet, SimplicialObject, diagonal`. Zero hits; `SimplicialObject` is
  unknown to that service. This is recorded as an unsuccessful query, not evidence
  that the notion is absent by itself.
- Grep in Mathlib/AlgebraicTopology:
  `bisimplicial|diagonal.*[Ww]eak|[Ww]eak.*diagonal`. Zero hits.
- LeanSearch: “A levelwise weak homotopy equivalence of bisimplicial sets induces
  a weak homotopy equivalence of diagonals”. Eight hits. The apparent diagonal
  hit is `SimplicialObject.diagonal`, whose full signature is a long edge
  `X _⦋n⦌ ⟶ X _⦋1⦌`, not the diagonal of a bisimplicial set. Other hits are
  general model-category statements.
- Direct `rg` searches for `bisimplicial`, `Bisimplicial`,
  `bisimplicialZerothRowIndex`, `bisimplicial_diagonal_equivalence`, and the item id
  in Mathlib, upstream `WeilConjectures`, project `lean/Sheaf`, and the upstream
  name index found no declaration defining this transformation or stating the
  theorem. The project has only textual references in `CosimplicialFrameMapping`.
  Searches for product diagonals and currying found the Mathlib constructions
  used here, so no duplicate diagonal, row, column, or currying definition is added.

Validation: the delivered file compiles through `scompile.py`, as a sandbox and
under its intended module path, with no errors or warnings. Every theorem proof
is `sorry`; the canonical helper has real data. The required delivery dry run
is run after preparing this record and report. Independent second reading is
left to the next worker as instructed.

## Second reading by N4

I read the node `lem-coef-bisimplicial-diagonal-equivalence`, its source place
(Cisinski, Theorem 3.1.16, printed pp. 79--81), and the complete Lean module
`Sheaf.AlgebraicTopology.BisimplicialDiagonalEquivalence`.

Object and hypothesis matching:

- The node's bisimplicial sets are functors
  `D : SimplexCategoryᵒᵖ × SimplexCategoryᵒᵖ ⥤ Type u`; the Lean binders use
  exactly this product functor category, with arbitrary explicitly bound `u`.
  A morphism in the node is a natural transformation `f : D ⟶ E`, exactly the
  Lean binder.
- The node's diagonal is the functor with value `D(n,n)` and simultaneous
  operators. Lean renders it as `whiskerLeft (Functor.diag SimplexCategoryᵒᵖ) D`,
  and the induced map as the same whiskering of `f`.
- The first node clause quantifies over every `D`, `E`, and `f`, assumes a weak
  homotopy equivalence on every row, and concludes a weak equivalence on the
  diagonal. Lean's
  `∀ m : ℕ, Enhanced.IsWeakHomotopyEquivalence
  (whiskerLeft (Prod.sectR (Opposite.op ⦋m⦌) SimplexCategoryᵒᵖ) f)` fixes the first
  index to `m` and is precisely that row map; its conclusion is the stated
  diagonal map.
- The exchanged clause has the same quantifiers and conclusion. Lean's
  `Prod.sectL SimplexCategoryᵒᵖ (Opposite.op ⦋n⦌)` fixes the second index and is
  precisely the node's columnwise hypothesis.
- The final clause quantifies over every `D` and assumes weak equivalence of
  every horizontal structure map. Lean's
  `∀ (m n : SimplexCategoryᵒᵖ) (a : m ⟶ n),
  Enhanced.IsWeakHomotopyEquivalence ((curry.obj D).map a)` is exactly the map
  `D(m,-) → D(n,-)` for every morphism in the first opposite simplex category,
  including identities and all faces and degeneracies. The conclusion is weak
  equivalence of `whiskerRight bisimplicialZerothRowIndex D`.
- The helper used in that conclusion is the canonical index map: at `n` its
  component is `(SimplexCategory.const n.unop ⦋0⦌ 0).op ×ₘ 𝟙 n`. Since
  `SimplexCategory.const n.unop ⦋0⦌ 0` is the unique map `[n] → [0]`, its
  opposite has the required direction from the zeroth row to the diagonal.
  Thus it is the node's specified map, not an arbitrary equivalence.

Every occurrence of weak equivalence is the dependency declaration
`Enhanced.IsWeakHomotopyEquivalence` supplied by
`lem-coef-kan-quillen-right-proper`; no Kan, fibrancy, connectedness,
nonemptiness, finiteness, characteristic, or Noetherian hypothesis was added.
The simplicial-set notion is the recorded Mathlib `SSet` notion from
`def-weil-pbc-simplicial-set`; no private replacement was introduced.

Edge cases checked: both `ℕ` quantifiers include degree zero; at degree zero
the unique `[0] → [0]` map makes the helper component the identity. Empty
bisimplicial sets, empty rows or columns, zero-dimensional simplices,
disconnected sets, and non-Kan sets remain allowed. The universe `u` is free,
and no universe equality or finiteness restriction is imposed. The exchanged
direction uses the same diagonal and induced map.

I repeated the duplicate searches with `msearch.py`, LeanFinder/Loogle and
`rg` over pinned Mathlib, the upstream `WeilConjectures` tree, and project
`lean/Sheaf`. The only diagonal hit was
`CategoryTheory.SimplicialObject.diagonal`, whose type is an internal map of a
single simplicial object; no bisimplicial diagonal weak-equivalence theorem or
the canonical zeroth-row index transformation exists. The existing dependency
declarations were opened and used directly. No mismatch was found, so no Lean
or node statement was changed. The module compiles cleanly with the required
`scompile.py` wrapper.
