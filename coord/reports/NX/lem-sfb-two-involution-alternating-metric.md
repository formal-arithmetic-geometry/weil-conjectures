## Worker report

The module `Sheaf.GroupTheory.TwoInvolutionAlternatingMetric` states
`Subgroup.two_involution_alternating_metric`, with its proof `sorry`. Four public helper
definitions spell out notation introduced in this very node: the alternating word,
the least representing length, the set of shortest words, and the displayed normal-form
list. These are helpers of this node's notion, not independent missing notions. Their
data is explicit, with no postponed definition proofs. No statement correction is made.

Hypothesis and clause correspondence:

- An arbitrary group is `{G : Type u} [Group G]`; `u` is explicit and unrestricted.
- The two elements are `(s t : G)`, with `hs : s ≠ 1`, `ht : t ≠ 1`, and `hst : s ≠ t`.
- The involution equations are `hs2 : s ^ 2 = 1` and `ht2 : t ^ 2 = 1`.
- Finite product order is `m : ℕ`, `hm : 0 < m`, `horder : orderOf (s * t) = m`.
  Mathlib's orderOf is the least positive exponent giving one, and is zero only for
  infinite order. Thus these binders are precisely the hypothesis in the node.
- The alphabet is the actual set `({s, t} : Set G)`. Membership of every letter is used
  in the length and shortest-word definitions. The dependency's Mathlib `Set.Finite`
  is the canonical notion of finite set; a pair set is automatically finite, so no
  additional finiteness assumption or tautological conclusion is introduced.
- `H` is `Subgroup.closure ({s, t} : Set G)`. Since each generator is its own inverse,
  this is exactly the subgroup of positive finite products specified by the node,
  including the empty product. This does not assume `H = G`.
- `twoInvolutionWord s t k` is the reverse of
  `CoxeterSystem.alternatingWord t s k`. The latter ends with `s`, so the reverse
  begins with `s`. Both zero-length words are definitionally `[]`. Swapping `s,t`
  gives `B_t(k)`. Their `List.prod` values are the node's `b_s(k), b_t(k)`.
- `twoInvolutionWordLength s t g` is `sInf` of the natural numbers `n` for which
  there is a length-`n` list of letters in the alphabet with product `g`. On `H` this
  set is nonempty, since inverses of the generators are generators. The infimum
  of a nonempty set of naturals is its minimum. Its total extension outside `H`
  is never used in a conclusion; no arbitrary representing word is chosen.
- `twoInvolutionShortestWords` records exactly the alphabet, product and minimal
  length conditions, retaining words themselves rather than just their products.
- `2 ≤ m` is the first conjunct. The next equates the two length-`m` products;
  `w_0` is explicitly represented throughout by `(twoInvolutionWord s t m).prod`.
- `twoInvolutionNormalForms` is `[1]`, followed by the two products at each length
  `j + 1` for `j` in `List.range (m - 1)`, followed by `b_s(m)`. For `m ≥ 2` these
  middle indices are exactly `1 ≤ k < m`. `List.Nodup` and the following membership
  equivalence with `closure` state that this list contains every element of `H`
  exactly once, including that every listed element belongs to `H`.
- The next two conjuncts are `d(1) = 0` and the exact shortest-word set `{[]}`.
- The universally quantified `k` clause with `1 ≤ k` and `k < m` gives both length
  values `k`, and the exact singleton shortest-word sets `{B_s(k)}`, `{B_t(k)}`.
- The final two conjuncts give `d(w_0) = m` and precisely the pair of shortest words
  `{B_s(m), B_t(m)}`. Distinctness of these two actual lists follows from their
  different first letters, `s ≠ t`, and `m ≥ 2`; a pair set therefore does not collapse
  the two words under any allowed input.
- There is no deletion, Coxeter presentation, finiteness of `G`, or generation-of-`G`
  assumption. All seven proof steps are reproduced in the theorem docstring.

Dependency declarations read and used:
`def-sfb-finite-infinite-set` is a Mathlib leaf whose mathlib_match is `Set.Finite`
in `Mathlib.Data.Finite.Defs`; the associated `Set.Infinite` is also read. The
recorded signatures are `Set.Finite (s : Set α) : Prop := Finite s` and
`Set.Infinite (s : Set α) : Prop := ¬s.Finite`. The module imports this dependency.
For word notation it uses `CoxeterSystem.alternatingWord` from
`Mathlib.GroupTheory.Coxeter.Basic`, whose full declaration takes only an arbitrary
`B : Type u` and elements of `B`: it does not take a CoxeterSystem. Consequently
using this list constructor introduces no presentation hypothesis. Other standard
interfaces are `Subgroup.closure`, `List.prod`, `orderOf`, `sInf`, and `List.Nodup`.

Edge cases checked before drafting: at length zero both reversed alternating words
are empty and have product one; the identity has length zero. For `m = 2` (commuting
distinct involutions) the list is `1,s,t,st`, with two longest words `st,ts` and unique
length-one words. For `m = 3` the list is `1,s,t,st,ts,sts` with `sts=tst`; the two
length-three lists remain distinct. Even `m = 2a` and odd `m = 2a+1` agree with the
four product formulas in proof step 3. Orders zero and one are excluded by precisely
the finite-order and distinctness hypotheses; the trivial group supplies no permitted
pair. The ambient group may be infinite and may contain elements outside `H`.

Searches (the prescribed msearch.py wrapper, group NX, this item):

- leanfinder: "Shortest words in a group generated by two distinct involutions whose
  product has order m are alternating words of length at most m". Eight hits include
  `CoxeterSystem.not_isReduced_alternatingWord`, `length`, `IsReduced`, and alternating
  product identities. These geodesic results require a CoxeterSystem, so do not give
  this theorem for an arbitrary pair of involutions.
- loogle: `"alternatingWord", "wordLength"` returned no hits. A further single-name
  `"alternatingWord"` query returned the generic list constructor and its identities;
  the constructor is reused, rather than duplicated.
- grep: `def.*(length|Length|alternatingWord)|def.*IsReduced` in GroupTheory returned
  seven hits: Coxeter length/reduced words, the alternating list, free-group reduced
  words and a nilpotency comment. None supplies an arbitrary-pair word metric.
- leansearch: "Least length of a word in a given generating set of a group" returned
  Coxeter length/reduced-word declarations and free-group length/norm declarations.
  None is the present arbitrary-group two-generator metric.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for `alternatingWord`,
  `two_involution`, `twoInvolution`, `wordLength`, `wordMetric`, `IsShortest` found
  no declaration for this node. Searching the node id in upstream Lean also found
  none. Searching DAG nodes by "shortest word", "least length", "word metric",
  and "alternating word" found this node and consumers or statements with deletion,
  root-system, or presentation hypotheses, not a duplicate definition/interface.
- Inspected Mathlib's `DihedralGroup` definition and Coxeter alternating-word source:
  a predefined dihedral model is not the classification of the arbitrary generated
  subgroup and all of its shortest words. Read the cited online Cashen pages 27–29:
  these are comparison examples with presentations and geometric actions; the node
  honestly supplies its own elementary argument for the arbitrary-pair statement.

No STATEMENT-DISPUTED flag or node fault was found. The supplied example
`Sheaf.CategoryTheory.CompactObject` is currently withdrawn, so the module follows the
explicit module/public-import/expose rules in the standing stage-2 brief instead.

Compilation uses scompile.py exclusively. The first compile found that `orderOf` is
not publicly supplied by Coxeter.Basic; an explicit public import of
Mathlib.GroupTheory.OrderOfElement repairs this missing import. Final results and
delivery validation are recorded below after completion.

Final scompile.py check passed for both the sandbox module and its library-path
compilation, with exit code zero and no errors or unexpected warnings. Explicit
`set_option autoImplicit false` verifies that every variable is bound; all source
lines are at most 100 characters. The node copy differs only in `lean`, including
all five owning declarations and the theorem signature verbatim.

## Second reading by NX

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
