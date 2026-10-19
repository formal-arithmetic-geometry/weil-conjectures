## Worker report

The module `Sheaf.Combinatorics.NonfreeChainCompletions` states
`SSet.nonfreeChain_completions`, with its proof entirely `sorry`. Its accompanying
real predicate `SSet.IsFreePrismChain` packages the definition of free explicitly
introduced by this very node; it is a helper belonging to this node, recorded in
`lean.declarations`, not a second independent notion. No definition uses postponed data.

Source read: https://kerodon.net/tag/01DN, Lemma the project server, proof's definition of free,
exhaustion paragraphs and final missing-face paragraphs. The node's elementary
finite-poset formulation extends the same argument to n=1, as checked directly.
All five steps of the node's proof are reproduced in the theorem docstring.

Hypothesis and clause correspondence:

- `m n : ℕ` and `hn : 1 ≤ n` give precisely the stated nonnegative m and positive n.
  Vertices are `Fin (m + 1) × Fin (n + 1)`, the two finite ordinals with all endpoints.
- `τ : List ...` is a finite sequence. `hchain` is pairwise coordinatewise ≤ with
  distinct vertices, exactly strict increase in the product partial order. In particular,
  equality of just one coordinate is allowed. Nonemptiness follows from `hfirst`
  (and already from `hfst`); it is not an additional restriction.
- `hfst` says every first coordinate occurs. `hsnd` says every positive second
  coordinate occurs, including n; it places no requirement on coordinate zero.
- `hnopair` excludes exactly the vertical zero-to-one pairs. Under `hn`, the numeral
  `1 : Fin (n + 1)` is the actual element of value one, without modular wraparound.
- `p`, `k`, `hfirst` and `hbefore` designate the first level-one vertex as `(p,1)`.
  `hbefore` excludes value one at every earlier position. Such a choice exists from
  `hsnd` and `hn`; no special case is added by making this designated vertex explicit.
- The first conclusion `k = p.val`, together with the mapped `take (k + 1)` equality,
  gives precisely `(0,0),...,(p-1,0),(p,1)` as the entire initial segment. Mapping to
  natural coordinate values only avoids dependent finite casts; `Fin.val` is injective.
- `IsFreePrismChain σ` expands to strict increase, surjectivity of both coordinate
  projections, and existence of a vertical zero-to-one pair, exactly the node's free
  condition. Its definition uses coordinate values rather than finite numeral one,
  so it is correct even at n=0 (where freeness is false).
- In the quantified equivalence, `∃ i x, i ≤ τ.length ∧ x ∉ τ ∧
  σ = τ.insertIdx i x` means insertion of exactly one new vertex. The index bound
  avoids List.insertIdx's out-of-bounds no-op. Together with freeness it describes
  precisely the free strict one-vertex extensions, without imposing a dimension bound.
- The right side lists exactly insertion of `(p,0)` at position p and insertion of
  `(b,1)` there when `b.val + 1 = p.val`. The latter is exactly b=p-1 with p>0;
  there is no such b when p=0. The reverse implication also asserts both displayed
  candidate chains really are free strict one-vertex extensions.
- The next two optional-index equalities place the first pair at p and p+1. The
  quantified membership equivalence says its vertical pair is unique, at coordinate p.
- The final clause, for every predecessor b of p, places the second pair at b=p-1
  and p and gives its uniqueness at coordinate b. Since the prefix is already fixed,
  these insertions are immediately before `(p,1)` and immediately after `(p-1,0)`.

Dependency: `def-weil-pbc-simplicial-set` is a Mathlib leaf with no Lean record.
I read the signatures/docstrings of its recorded `SSet`, `SSet.degenerate`,
`SSet.nonDegenerate`, `SSet.Subcomplex`, and `SSet.Finite`. The node here uses
only its finite ordinal convention, realized by `Fin (r + 1)` in SimplexCategory.
The dependency's defining module `Mathlib.AlgebraicTopology.SimplicialSet.Basic`
is publicly imported; no copy of a simplicial-set definition is introduced.
`Mathlib.Data.List.InsertIdx` supplies the standard list insertion operation.
There are no proof dependencies, dependency repairs, new nodes or statement changes.

Edge cases: m=0 is allowed; n=1 is allowed; p=0 gives the singleton initial prefix,
no second completion, and the newly inserted point supplies level zero. p=m causes
no issue; neither the successor of p nor a point beyond m is required. An empty τ
cannot meet the hypotheses. Explicit enumeration of all strict product chains for
0≤m≤3 and 1≤n≤3 checked all 110 admissible τ and 156 completions: exact prefixes,
both directions of the classification, pair positions and uniqueness all passed.
The direct mathematical argument in the docstring covers arbitrary sizes.

Searches made:

- msearch.py leanfinder, “Strict product ordinal chain with exactly two free one point
  completions”: eight Profinite/Nobeling good-product or induction results. None
  classifies the free completions in this node.
- msearch.py leansearch, “A chain in a product of finite ordinals has two free one
  vertex completions”: eight OmegaCompletePartialOrder chain/zip/supremum results,
  concerning countably infinite weak chains; no exact match.
- msearch.py loogle, `List.insertIdx`: twelve results, including the exact insertion
  operation and its elementary length/erasure lemmas. Used the existing operation;
  none states this product-chain classification.
- msearch.py grep, `def IsIndex|def IsType₂|nonfree` in AlgebraicTopology/SimplicialSet:
  three hits in UnionProd.lean. I read IsIndex and the surrounding pairing interface:
  it concerns a fixed simplex and a horizontal horn pairing, not classification of
  these two vertical free completions.
- Direct rg over WeilConjectures and lean/Sheaf for nonfree/vertical-pair/free-chain
  vocabulary found no exact declaration; the free-chain hits concern module complexes.
  The item-id search in WeilConjectures was empty. Exact-name rg for
  `IsFreePrismChain|nonfreeChain_completions` over Mathlib, upstream, the project's
  Lean and dag/lean_names_upstream.json was empty.

Verification: the prescribed scompile.py compiled this delivered file cleanly in
both sandbox and library modes. Only the theorem remains postponed, as required.
No STATEMENT-DISPUTED or node fault was found.

## Second reading by Q148

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
