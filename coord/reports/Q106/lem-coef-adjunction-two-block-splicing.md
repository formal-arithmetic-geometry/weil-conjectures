## Worker report

The module `Sheaf.CategoryTheory.AdjunctionTwoBlockSplicing` states
`CategoryTheory.AdjunctionWord.two_block_splicing`, with its sole proof `sorry`.
It adds no definitions and proves nothing. The natural-language statement, proof,
and proof dependencies are unchanged. The already published
`lem-coef-adjunction-block-run-collapse` is added to `stmt_deps`, as authorized for
landed nodes: its definitions are now used in the statement as well as its theorem
in the proof plan. No dependency node or module needs repair.

Source read: Riehl--Verity, *Homotopy coherent adjunctions and the formal theory of
monads*, https://emilyriehl.github.io/files/adjunctions.pdf, Proposition 3.2.2 and
proof, printed pp. 824--825 (PDF pp. 23--24). The Segal square uses the two vertex
blocks and their common vertex, and the proof specifies splicing with unique
preimage. The explicit integer-word coordinate statement being rendered here is
the node's expansion of that splicing. I also read the item, the entire statement
and Lean record of `def-cbc-enhanced-diagrams-cones`, the full published
`AdjunctionBlockRunCollapse.lean` (using `scompile.py --source` and then the refreshed
shared source), and its node and proof.

Hypotheses and clauses, in the order of the node:

- Standard simplices and their monotone coordinates use the imported
  `Sheaf.CategoryTheory.EnhancedDiagramsCones` and its Mathlib `SSet.stdSimplex`.
  The introductory vertex inclusions `i ↦ i` and `i ↦ m+i` identify which block
  restrictions are intended; their interval maps are exactly the two maps below,
  as explained in the module docstring. The result is the displayed word bijection,
  so no arbitrary simplicial map or geometric hypothesis is a theorem parameter.
- Dimensions `r ≥ 0` are natural numbers in the reused `IsWord`. The theorem binds
  `(m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n)`, exactly `m,n ≥ 1`.
- The two signs are `(p q : Bool)`, with `false = -`, `true = +`, using the published
  convention. All four choices are quantified, with no equality restriction.
- `W_r(p,q)` is `{c : List ℕ | IsWord r p q c}`. In the source of this predicate,
  `∀ j ∈ c, j ≤ r+1` imposes the alphabet (nonnegativity is intrinsic to `ℕ`);
  `head? = some (if p then r+1 else 0)` fixes the first letter and nonemptiness;
  `getLast? = some (if q then r+1 else 0)` fixes the last letter; and
  `IsAlternating p c` gives `<` at even indices when `p=false`, `>` at odd indices,
  with the inequalities reversed when `p=true`. Its quantified condition only
  applies when `i+1 < c.length`, so singleton strings are included.
- `R` is the published `AdjunctionWord.reduce`, not a new reduction. Its
  `eraseFirstPair` scans from the left, deletes the first adjacent equal pair,
  and repeats with initial-length fuel, which suffices since each deletion removes
  two letters. It allows the empty output. All words fed to `R` here are in the
  nonnegative integer alphabets on which the node needs it; the same pair-deletion
  algorithm is used without any additional reduction condition.
- `L(j)=min(j,m+1)` is `lowerRestriction m`; `U(j)=max(j-m,0)` is
  `upperRestriction m`, whose natural subtraction is truncated at zero.
  `List.map` is entrywise application. Thus the literal function in `Set.BijOn`
  is precisely `c ↦ (R(L_*c), R(U_*c))`.
- The domain in `Set.BijOn` is exactly `{c | IsWord (m+n) p q c}`.
  The codomain is the subset of pairs `ab : List ℕ × List ℕ` satisfying
  `IsWord m p q ab.1 ∧ IsWord n p q ab.2`, followed by the compatibility equation.
- The first endpoint map `v` is the lambda `fun j : ℕ ↦ if j ≤ m then 0 else 1`.
  On the first component's bounded alphabet the only remaining value is `m+1`,
  so this is exactly the stated `v`. The second map `t` is the lambda
  `fun j : ℕ ↦ if j = 0 then 0 else 1`, exactly zero at zero and one for `j>0`.
  The compatibility clause is literally
  `reduce (ab.1.map v) = reduce (ab.2.map t)`.
- Mathlib `Set.BijOn` is defined as `MapsTo ∧ InjOn ∧ SurjOn` in
  `Mathlib/Data/Set/Operations.lean:322`. Consequently it asserts that the specified
  map lands in precisely this compatible set, is injective on `W_(m+n)`, and
  reaches every compatible pair. The `MapsTo` clause in particular asserts both
  reduced restrictions are nonempty with the required endpoints and strict
  alternation: those are part of the codomain's two `IsWord` predicates. There is
  no weaker range-only or abstract existence-of-an-unspecified-bijection assertion.
- Lists have arbitrary finite length. Neither the theorem nor `IsWord` bounds
  their length or requires any internal letter to occur.

Dependency declarations used:

- `Sheaf.CategoryTheory.EnhancedDiagramsCones`, the recorded module of
  `def-cbc-enhanced-diagrams-cones`: standard-simplex convention uses its imported
  Mathlib `SSet.stdSimplex`; I read the full signature and docstring of its recorded
  main declaration `SSet.Enhanced.coneCategory`. This cone definition is unrelated
  to the finite calculation and is not replaced or specialized.
- `Sheaf.CategoryTheory.AdjunctionBlockRunCollapse`:
  `CategoryTheory.AdjunctionWord.IsWord`, `IsAlternating`, `lowerRestriction`,
  `upperRestriction`, and `reduce` are reused verbatim. The recorded theorem
  `CategoryTheory.AdjunctionWord.block_run_collapse` is the proof dependency used
  in every one of the five docstring proof steps; its full signature and docstring
  were read. Because its word definitions now occur in the signature, its module
  is a public import, and its landed node is also a statement dependency.
- Mathlib `Set.BijOn` is imported from its defining `Mathlib.Data.Set.Operations`.

Edge cases checked before drafting: an empty input is excluded by the `some`
endpoint conditions; a singleton is accepted exactly when the signs agree and
its sole entry is their endpoint; the two singleton restrictions agree; all four
sign choices are included; words using just endpoints or omitting interior
letters remain allowed; words can repeat endpoint letters internally; `m=n=1`
is included. The premise deliberately excludes zero block dimensions, exactly
as the node does. The reusable `IsWord` itself still includes `r=0`.

The scratchpad independently enumerated all source words of length at most 9 for
`(m,n) = (1,1), (1,2), (2,1), (2,2), (1,3), (3,1)` and every `p,q`. It checked
membership, compatibility and injectivity in 83,134 cases. It also enumerated
all compatible pairs with each component of length at most 6 and checked the
run-interleaving inverse in 4,026 cases. It tested reductions `[1,1] → []`,
`[1,1,1] → [1]`, and `[1,2,2,1] → []`. All checks passed. These finite checks are
only edge-case validation; the Lean theorem remains postponed as required.

Searches actually run:

- `msearch.py ... leanfinder`, query "Reduced alternating ordinal strings are in
  bijection with pairs of reduced interval restrictions having equal boundary
  reductions": eight hits on Nobeling ordinal/projection constructions, none on
  this statement.
- `msearch.py ... loogle`, query `List, Function.Bijective`: nine hits including
  `List.reverse_bijective`, `Function.Bijective.list_map`, `List.map_bijective_iff`,
  and free-group inverse reversal. These signatures do not state the block splice.
- `msearch.py ... grep`, query `splice|splicing|alternatingWord|undulating` in
  `AlgebraicTopology/`: zero hits.
- `msearch.py ... leansearch`, query "Bijection between strictly alternating
  ordinal words and compatible reduced two block restrictions": eight hits,
  including `CoxeterSystem.alternatingWord`, ordinal order isomorphisms, and
  Nobeling projection results. None has these words or restriction maps.
- `rg` on `lean/Sheaf`, upstream `WeilConjectures`, and
  `dag/lean_names_upstream.json` for the exact item id, `two_block_splic`,
  `twoBlockSplic`/`two block` naming patterns, and `AdjunctionWord` found the
  published run-collapse helpers but no existing splicing theorem. Upstream
  `WeilConjectures` has no item-id attachment or matching theorem.
- Direct Mathlib `AlgebraicTopology` search for `splice|splicing|undulating` found
  no match. The full helper source confirms that `block_run_collapse` only gives
  the run calculation, not this bijection.

There are no statement disputes or statement corrections. No new nodes or
additional dependency modules were necessary. The source module compiled cleanly
through the required `scompile.py Q106 lem-coef-adjunction-two-block-splicing`
wrapper, including compilation in sandbox and library positions.

## Second reading by Q106

This is the author's second pass, not an independent-worker review; the dispatcher
brief assigns independent delivery review to the maintainer and forbids spawning
other agents. Reopened the JSON statement and the complete module and checked the
following: the source dimension is `m+n`, the two target dimensions are `m` and
`n`; the upper alphabet map subtracts `m` (not `m+1`); the endpoint map of the left
word cuts at `m`, whereas that of the right word cuts at zero; the same `p,q`
occur in all three word predicates; `Set.BijOn` includes landing in the target,
not just injectivity/surjectivity; the target includes the displayed compatibility
in addition to both word conditions. Singleton and arbitrary-length cases are
retained by the reused `IsWord`. All five proof steps, with the run-collapse node
and the inverse construction, are present in the theorem docstring. No mismatch
was found. The only DAG addition is the already landed run-collapse node in
`stmt_deps`, because its definitions are now explicit statement dependencies.
