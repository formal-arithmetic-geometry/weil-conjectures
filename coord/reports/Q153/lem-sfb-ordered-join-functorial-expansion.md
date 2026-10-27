## Worker report

The module `Sheaf.AlgebraicTopology.OrderedJoinFunctorialExpansion` states
`AlgebraicTopology.OrderedJoin.functorialExpansion`, with `sorry`, and constructs the
unreduced per-summand list `AlgebraicTopology.OrderedJoin.summandRecipe` with real data.
There are no new mathematical notions, dependency repairs, or statement corrections.
Only the item's `lean` record changes. The source is the current
`literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/sk-thm-sf-ctf-stability-direct-images.proof.md`,
paragraph (3), read in full. As the node explicitly says, the ordered-join calculation
is an agent expansion below that paragraph, not a claim made in the blueprint.
The six accepted node proof steps are reproduced as the theorem's proof docstring.

Hypotheses and constructions, clause by clause:

- `r : ℕ` and `hr : 1 ≤ r` are the stated positive number of colors.
  `Fin r` is exactly I={0,...,r-1}, with its usual increasing order.
- `X : Fin r → Type u` and `v : ∀ i : Fin r, X i` are the arbitrary sets and
  their specified points. The universes `u v` and every variable are explicit;
  `set_option autoImplicit false` is present.
- The existing `Face X` stores a finite color set and a vertex at each of its
  colors. The increasing order of the color set specifies exactly the displayed
  ordered symbol. `Symbol X q` imposes `(colors.card : ℤ) = q + 1`.
- `Chain X q` is `Symbol X q →₀ ℤ`, with the specified integer basis
  `Finsupp.basisSingleOne`; a basis element is `Finsupp.single σ 1`.
  This is the basis notion in `def-weil-pbc-free-module`, not an unspecified free
  object. The unique empty face is degree -1. There are no symbols below -1 or
  at or above r, so those chain modules are zero. This represents precisely the
  augmented degree convention, without a nonnegative-degree restriction.
- The existing `insertion v i q (q+1)` is c_i: zero if color i is present;
  otherwise its value is `positionSign C i` times the inserted symbol.
  `positionSign C i = (-1)^((C.filter (fun j ↦ j < i)).card)` is exactly (-1)^k_i.
- The existing `remainder v i q` is R_i: zero if color i is missing, and otherwise
  the original symbol minus its color-i replacement. Both maps use
  `Finsupp.linearCombination ℤ` for integer linear extension. `symbolTerm`
  returns zero when the target-degree cardinality fails, and maps from zero
  source modules are zero. Thus all the stipulated zero components are retained.
- `remainderPrefix v n q` is the existing fold-right definition of P_n. It is
  the identity for n=0 and R_0 composed with ... with R_(n-1) for n≤r, with the
  rightmost factor applied first. Each individual summand uses
  `remainderPrefix v i.val (q+1)` after `insertion v i q (q+1)`.
- `Y : Fin r → Type v` and `f : ∀ i : Fin r, X i → Y i` quantify over every
  vertex-map family, including maps between different type universes. There is
  no injectivity condition. The target chosen point is literally
  `fun j ↦ f j (v j)`. Existing `chainMap f q` applies f vertexwise, preserves
  colors and fixes the empty face, and extends by integer linearity.

Conclusions, clause by clause:

- The first conjunct quantifies over Y, f, every integer q and each color i.
  Its first equality of composed linear maps is exactly
  J_(q+1)(f)c_i^v = c_i^(f(v))J_q(f).
  Its second equality is J_q(f)R_i^v = R_i^(f(v))J_q(f).
- The second conjunct quantifies over every integer q, basis symbol σ and color i.
  Its first implication uses exactly
  `i ∈ σ.val.colors ∨ ∃ j : Fin r, j < i ∧ j ∉ σ.val.colors`,
  and concludes P_i c_i[σ]=0. This is both asserted vanishing cases.
- The next implication assumes exactly the complementary conditions:
  `i ∉ σ.val.colors` and `∀ j : Fin r, j < i → j ∈ σ.val.colors`.
  Its equality evaluates the list `summandRecipe r σ.val.colors i` by mapping
  each entry `(coefficient, (insertion color, replacement subset))` to
  `coefficient • symbolTerm X (q+1) (replaceColors v A (insert v i σ.val))`
  and taking `List.sum`. Thus σ_(i,A) inserts the chosen vertex first and then
  replaces precisely the vertices of colors A, exactly in the stated order.
- The real definition `summandRecipe` lists each member of
  `(Finset.univ.filter (fun j : Fin r ↦ j < i)).powerset.toList`, with coefficient
  `(-1 : ℤ)^((C.filter (fun j ↦ j < i)).card + A.card)`, insertion color i,
  and replacement subset A. This is exactly the exponent k_i+|A| and the
  specified subset indexing. There is no sum or deduplication in this recipe.
  `List.map` keeps all entries even when their evaluated symbols agree.
- The final conjunct states `(summandRecipe r C i).length = 2 ^ i.val` for every
  color set and color. The recipe's signature has only r, C and i, and its
  body tests only colors, so the coefficient/insertion/replacement data has no
  dependence on original or chosen vertex values. In particular it requires
  no decidable equality on the sets X_i. This is a concrete list, not an
  existential assertion that some unexamined formula has the right sum.

Dependency declarations read and used:

- `Mathlib.LinearAlgebra.FreeModule.Basic`, `Module.Free`: the recorded dependency
  `def-weil-pbc-free-module`, read with its full class signature and docstring.
- `Mathlib.LinearAlgebra.Finsupp.VectorSpace`, `Finsupp.basisSingleOne`: the exact
  basis of integer functions with finite support, read with its signature and
  defining `Basis.ofRepr (LinearEquiv.refl _ _)`.
- `Sheaf.AlgebraicTopology.OrderedJoinPartialContraction`, namespace
  `AlgebraicTopology.OrderedJoin`: `Face`, `Symbol`, `Chain`, `symbolTerm`,
  `insert`, `replaceColors`, `positionSign`, `insertion`, `remainder`,
  `remainderPrefix`, `mapFace`, and `chainMap`. The entire module and each
  declaration's signature and docstring were read locally and checked against
  current server source with `scompile.py --source`.
  These are precisely the constructions already explicitly introduced in this
  item's natural-language statement. They are reused without private copies;
  no assertion of the parent theorem `partialContraction` is used. In particular
  the new theorem is not deduced by a circular invocation of its downstream
  parent. The DAG fields remain unchanged. If proof-dependency imports are added
  to the parent later, the stage-2 rule to omit an import closing a module cycle
  applies: the parent already owns these shared data definitions.

Edge cases checked before drafting: the empty face has q=-1; only i=0 survives
and its powerset contains only the empty subset. A top face contains every
color, hence every summand vanishes, including when the target chain module is
zero. With r=1 the same two cases exhaust the symbols. If chosen and original
vertices agree, repeated list entries remain and can cancel only upon summing.
Noninjective maps can collapse distinct vertices and do not change any color or
insertion position. Degrees q<-1 and q≥r have no symbols, so all maps from them
are zero. P_0 is the empty fold, and P_r is defined by the same existing prefix
construction. No assertion requires inserting a nonexistent color r.

An additional finite arithmetic check evaluated all faces over X_i={0,1}, all
choices of basepoints, all colors, and r=1,2,3,4: 5910 summand cases agreed with
the stated subset expansion or vanishing. For each case, both naturality
identities were also checked for the collapse-to-zero and flip maps. This is
an edge-case check, not a Lean proof; the delivered theorem remains `sorry`.

Searches made, with real service results recorded by msearch.py:

- LeanFinder: "Signed basepoint insertion and vertex replacement on ordered
  colored join chains commute with arbitrary maps and have an unreduced subset
  indexed expansion". Eight hits, including simplicialInsert and admissible
  simplex normal forms; none gives these operators or this statement.
- Loogle: `"Finset", "prod_sub"`. Twelve hits, including `Finset.prod_sub` and
  `prod_sub_ordered`. Their signatures concern scalar products in commutative
  rings and do not give the ordered replacement operators or naturality.
- LeanSearch: "Naturality of signed insertion and vertex replacement on free
  abelian ordered colored join chains and expansion over subsets". Eight hits,
  including categorical join and alternating-map insertion results; none is
  this statement.
- msearch grep of Mathlib: `(orderedJoin|coloredJoin|colouredJoin|insertionRemainder)`
  and `orderedJoinFunctorialExpansion|summandRecipe`, both zero hits.
- Additional LeanSearch and LeanFinder queries for the free ordered-join chain
  construction returned free groups and simplex insertion normal forms, not
  this construction or statement.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for ordered-join,
  colored-chain and insertion/remainder patterns found the exact reusable
  `OrderedJoinPartialContraction` module above. Its `partialContraction` states
  only naturality of the sum and expansion of the sum, and therefore is not an
  existing declaration for the present individual-operator/summand statement.
- A literal search for this item's id in `lean/WeilConjectures` found no declaration.
  DAG searches and `tools/blueprint_refs.py search 'ordered join'` found no
  independent definition node; the latter returned zero blueprint-node matches.
  The ancestor command returns None, consistently with the inherited agent
  expansion metadata. No duplicate definition node is introduced.

Validation: the required scompile.py compiled the delivered module in both its
sandbox and final library module identities, cleanly (2.0 s and 1.0 s). No warnings
or errors were reported. All source and node files in the shared repository were
read-only throughout; writes are confined to the assigned delivery sandbox.

## Second reading by Q153

A second pass by the same assigned worker compared the complete node statement
with the module and the imported definitions. No second agent was started, as
required by the dispatcher; the maintainer's independent review remains separate.
This pass checked the signs against k_i+|A| (rather than an incorrectly shifted
sign), the rightmost-first prefix order, target degree q+1 in the prefix, both
vanishing alternatives, insertion before replacement in σ_(i,A), and the exact
2^i cardinality rather than a bound. It also checked the two naturality formulas
are about c_i and R_i themselves, not merely their sum, and that no injectivity,
vertex equality, degree restriction, or extra structure on X_i was introduced.
The list is material data indexed by subsets and remains unreduced even for
coincident output symbols. No mismatch or statement correction was needed.
