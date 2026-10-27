## Worker report

The module `Sheaf.GroupTheory.InvolutionTwoDescentPrefix` states
`Group.exists_alternating_prefix_of_two_left_descents_of_deletion`, with one `sorry`
and no definitions or proofs. The original node is unchanged except for `lean`.
No statement correction or dispute was needed.

Clause-by-clause correspondence:

- The group is `{G : Type u} [Group G]`, with independent index universe
  `{I : Type v} [Finite I]`. A finite index type represents the node's finite set;
  `Set.Finite` is definitionally `Finite` on the corresponding subtype.
- The indexed generators are `t : I → G`; injectivity is `ht`, nonidentity is
  `hne`, involutivity is `hinvol`, and generation is
  `hgen : Subgroup.closure (Set.range t) = ⊤`.
- A word is `A : List I`; its product is `(A.map t).prod`, whose empty value is
  the identity. The function `ℓ : G → ℕ` is specified exactly by `hlength`:
  `IsLeast {n | ∃ A, (A.map t).prod = g ∧ A.length = n} (ℓ g)` for every `g`.
  Thus this binder is a way to introduce the uniquely specified minimum in the
  node, not an arbitrary length assumption. `IsLeast` includes attainment and
  minimality. Existence of positive representing words follows from generation
  and the involution assumption. This is the same specification style as the
  landed `Subgroup.exists_reduced_subword_extension_of_strong_exchange`
  (`Sheaf.GroupTheory.StrongExchangeSubwordExtension`); its specialized real-linear
  group theorem is not imported or restated here.
- A word is reduced precisely when its length equals `ℓ` of its product.
  `hdeletion` applies to every word for which this equality fails. Its positions
  satisfy `a < b` and `b < A.length`, and
  `(A.eraseIdx b).eraseIdx a` removes these original positions simultaneously:
  removing the larger first leaves the smaller position unchanged. Position zero
  corresponds to the source's position one.
- Distinct indices are `i j : I` and `hij : i ≠ j`. The finite product order is
  `m : ℕ`, `hm : 0 < m`, `horder : orderOf (t i * t j) = m`.
  Mathlib's zero order denotes infinite order; positivity excludes precisely that
  case. No separate finite-group or presentation assumption appears.
- Mathlib's `CoxeterSystem.alternatingWord a b m` alternates and ENDS in `b`.
  Therefore `(alternatingWord j i m).reverse` is exactly the node's `A_i`,
  and `(alternatingWord i j m).reverse` is `A_j`. The definition needs no
  `CoxeterSystem`, Coxeter matrix, or presentation, despite its namespace.
- The element is `g : G`; `hi` and `hj` cast BOTH lengths to integers before
  subtracting one, so the node's explicit integer interpretation is preserved.
- The witness `h : G` has both required product equalities and
  `ℓ g = m + ℓ h`, as the first three conjuncts.
- The final universal clause ranges over EVERY `C : List I`, with hypotheses
  `(C.map t).prod = h` and `C.length = ℓ h`. Its four conjuncts say the product
  of each concatenation is `g` and each concatenation has length `ℓ g`.
  Given the product equality, this is exactly that each is a reduced word for `g`.

Dependency declarations and interfaces read:

- `def-sfb-finite-infinite-set` is a Mathlib-status dependency with
  `mathlib_match = Set.Finite`, not a missing Lean attachment. Read its definition
  and docstring in `Mathlib.Data.Finite.Defs`: finiteness is `Finite` of the set
  subtype, hence `[Finite I]` is the exact type-indexed formulation. `Set.Infinite`
  in the same module is not needed by this finite-index statement.
- `Mathlib.GroupTheory.Coxeter.Basic`: read the general `alternatingWord`
  definition/docstring and its length and successor identities. Read the
  `CoxeterSystem` structure and `wordProd` signature to distinguish those
  presentation-dependent interfaces, which are not used here.
- `Mathlib.GroupTheory.OrderOfElement`: `orderOf` gives the least positive
  annihilating exponent, with zero for infinite order.
- `Mathlib.Order.Bounds.Basic`: `IsLeast` supplies membership and the lower-bound
  property. `List.map`, `List.prod`, `List.reverse`, `List.eraseIdx`, append and
  subgroup closure are Mathlib's existing constructions.
- Both proof dependency nodes were read. Neither
  `lem-sfb-deletion-parabolic-coset-length` nor
  `lem-sfb-two-involution-alternating-metric` has a Lean record in the read clone.
  Their imports are consequently absent; the complete four-step natural-language
  proof in the theorem docstring names both inputs for stage 3. Neither is a
  statement prerequisite: the theorem does not refer to their conclusions or
  introduce their restricted-length function.

Edge cases checked before writing:

- Empty `I` and the trivial group are not excluded by the universe or type
  encoding; there can be no distinct pair of indices under the hypotheses.
  Single-generator groups likewise have no pair `i ≠ j`.
- At `g = 1`, an integer descent would require a nonnegative natural length to
  equal `-1`; the hypotheses correctly fail. Natural subtraction would have
  introduced a spurious identity case, and is not used.
- `m = 0` is excluded precisely because finite order is requested. `m = 1` is
  impossible for distinct involutions with injective indexing, not excluded by
  an extra bound. Commuting distinct involutions (`m = 2`) are included.
- For `m = 2`, the reversed words are `[i,j]` and `[j,i]`; for `m = 3` they are
  `[i,j,i]` and `[j,i,j]`. This checks orientation for both parities.
- The empty tail `C = []` is permitted, including `h = 1`. The conclusion is
  universal over reduced tails rather than asserting just one chosen tail.
- Deletion permits the first and last positions, and words of lengths zero or
  one have no two valid positions. The least-length specification and generator
  hypotheses ensure such words are already reduced.

Searches for an existing statement or notion:

- `msearch.py leanfinder`: “Under the deletion condition two left descents give a
  common reduced alternating prefix of length the order of the product of two
  involutions”: eight Coxeter-system alternating-product/inversion hits, none
  with deletion-only hypotheses.
- `msearch.py loogle`: `"length", "alternatingWord"`: one hit,
  `CoxeterSystem.length_alternatingWord`, which is list length, not this theorem.
- `msearch.py grep`, query `wordLength|WordLength|deletion|Deletion|two.*[Dd]escent`
  in `GroupTheory`: zero hits.
- `msearch.py leansearch`: “The word length with respect to a set of generators
  in a group”: eight hits, including `CoxeterSystem.length`, `FreeGroup.norm`,
  and `GroupSeminorm`. These either assume a Coxeter presentation, describe free
  groups only, or do not specify this word metric.
- `msearch.py leanfinder`: “minimum length of a positive word in an arbitrary
  indexed family of group generators”: eight free-group/Coxeter-system hits,
  no general interface. The output records are in the sandbox `searches.jsonl`.
- Direct `rg` of Mathlib GroupTheory and the actual Coxeter signatures confirms
  no deletion-to-prefix theorem. Direct `rg` of both `lean/WeilConjectures` and
  `lean/Sheaf`, and of `dag/lean_names_upstream.json`, found no matching theorem,
  arbitrary indexed word-length declaration, or duplicate declaration name.
  The exact item-id search in `lean/WeilConjectures` found no match.
- DAG searches for word-length/word-metric/deletion definition nodes found no
  existing definition needed here. `tools/blueprint_refs.py search 'word length'`
  found zero blueprint nodes; `ancestor` reports the inherited null ancestor.
  The existing shuffle-word definition is about binary shuffles, not this metric.

Source reading: the node explicitly records an agent-written supporting argument
and unavailable local Bourbaki/Cashen copies. Read the author-hosted Cashen PDF
at https://www.mat.univie.ac.at/~cashen/Notes_on_Coxeter_groups.pdf,
Chapter 4 §4, Lemma 4.0.14(2), printed pages 120--121: the subgroup factor precedes
its minimum-length left-coset representative and lengths add. Its general Coxeter
hypothesis is not imported into the present deletion-only theorem. The node's
four-step elementary supporting argument is preserved in the Lean docstring.
The current `literature/blueprint/latest` has no occurrence of this supporting
node, consistent with the node's source and split report.

Validation: `scompile.py Q31 lem-sfb-involution-two-descent-prefix` compiled the
module separately in sandbox and library contexts on the server, without errors
or unexpected warnings. All variables and universes are explicit and
`autoImplicit` is disabled.

## Second reading by Q31

Author's second reading, with the original JSON and complete module open; no
independent worker was started, as the dispatch brief prohibits other agents.
The maintainer supplies the independent review.

Checked every hypothesis and conclusion against the mapping above. The main
potential mismatches were the end-letter convention of Mathlib's alternating
word and truncated natural subtraction. The statement handles these explicitly
by reversal and casts to integers. `hlength` is the exact attained-minimum
specification; it neither supplies a different metric nor strengthens the
hypotheses. There is no extra `CoxeterSystem` or chosen group presentation.
The conclusion retains both product equalities, additive length and every
reduced tail. Finiteness is the dependency's finite-set notion under the standard
set/type identification. No mismatch remained, and no node correction, new
node, or dependency repair was needed.
