## Worker report

The module `Sheaf.GroupTheory.DeletionParabolicCosetLength` states
`Monoid.deletion_parabolic_coset_length`, with its sole proof `sorry`.
The companion module defines `Monoid.generatorWordLength` by the actual natural-number
infimum of the lengths of representing lists. No data depend on a postponed proof.

Hypothesis and clause correspondence:

- The group is `{G : Type u} [Group G]`; the arbitrary index set is `{I : Type v}`.
  `[Finite I]` says precisely that `(Set.univ : Set I).Finite`: the dependency's
  `Set.Finite` is defined as finiteness of its subtype. This imposes no enumeration,
  decidable equality, nonemptiness, or relation between `u` and `v`.
- The indexed generators are `t : I → G`. `hinj` renders injectivity, `hne`
  renders nonidentity, `hinvol` renders `t_i² = 1`, and `hgen` renders generation
  as `Subgroup.closure (Set.range t) = ⊤`.
- A word is `List I`; its product is `(A.map t).prod`, including the empty product.
  `generatorWordLength t g` is the minimum from the node, by `Nat.sInf_def`.
  Generation by involutions implies that every `g` has a positive word: inverse
  generators equal the generators themselves. Thus the default on an empty set
  of possible lengths never occurs here.
- `hdelete` quantifies over every word longer than its minimum. Its witnesses
  satisfy `a < b` and `b < A.length`; these are exactly two distinct positions.
  `(A.eraseIdx b).eraseIdx a` removes precisely those original positions,
  with no index shift at `a` because the larger position was removed first.
  The displayed product equality is exactly the deletion hypothesis.
- `J : Set I` is arbitrary. The node's subgroup `H_J` is the standard
  `Subgroup.closure (t '' J)`. It equals products of `J`-words: these contain
  the identity, concatenate, and invert by reversing involutive letters.
  Hence membership in this closure is exactly the node's word-based membership.
- Restricting the alphabet is `fun j : J ↦ t j`. Every list of subtype elements
  is exactly a word in `J`, and conversely. The first conjunct quantifies over
  every subgroup element and asserts `ell_J(u) = ell(u)`.
- The second conjunct quantifies over every `h : G` and assumes, for every
  `v ∈ H_J`, `generatorWordLength t h ≤ generatorWordLength t (v * h)`.
  It then asserts, for each `u ∈ H_J`, exactly
  `ell(u*h) = ell_J(u) + ell(h)` in this order.
- No presentation, Coxeter matrix, order restriction, uniqueness assertion, or
  finite-group hypothesis was introduced. No statement correction was needed.

Dependency declarations read and used: `Set.Finite` (and accompanying
`Set.Infinite`) in `Mathlib.Data.Finite.Defs`, whose signatures and docstrings
were read at lines 183–206; finiteness of an index type is the equivalent Mathlib
`Finite` predicate. The additional definition node supplies
`Monoid.generatorWordLength` from `Sheaf.GroupTheory.GeneratorWordLength`.
Standard interfaces used directly include `List.map`, `List.prod`, `List.eraseIdx`,
`Subgroup.closure` from `Mathlib.Algebra.Group.Subgroup.Lattice` and the natural
infimum from `Mathlib.Order.Lattice.Nat` (`Nat.sInf_def`, `Nat.sInf_mem`).
There are no recorded proof-dependency modules to import.

Edge cases checked before writing: if `J = ∅`, its closure is the identity
subgroup and the empty word gives length zero, so both conclusions specialize
correctly. If `I = ∅`, generation forces `G` to be trivial; the theorem has no
`Nonempty I` or `Nontrivial G` binder. In a trivial group, nonidentity forces `I`
to be empty, which is allowed. If `J = Set.univ`, restricted and ambient words
are the same alphabet, and minimality forces `h` to have length zero. Repeated
letters in words are permitted. A word of length zero or one has no deletion
pair; such a word cannot be longer than its minimum under these assumptions.
For a two-letter word with equal involution letters, deletion yields the empty
word, represented correctly by the zero-based index pair `(0,1)`.

Searches: the prescribed `msearch.py` LeanFinder query on deletion and parabolic
coset additivity returned only CoxeterSystem results. Its signatures were checked
against `Mathlib/GroupTheory/Coxeter/Length.lean` and `Basic.lean`: they require
a presentation, absent here. Loogle `wordLength, wordNorm, CoxeterSystem.length`
returned zero hits (unknown `wordLength`). LeanSearch on a minimum-length list
of arbitrary monoid generators returned `CoxeterSystem.length`, `IsReduced`,
list product bounds, and free-monoid length, none the general notion. A further
LeanFinder query on arbitrary-monoid minimum word length again returned only
CoxeterSystem facts. Both prescribed grep searches returned zero matches.
Local `rg` of Mathlib for wordLength/wordNorm/word_length/word length found only
CoxeterSystem's specialized definition; `rg` of `lean/WeilConjectures` and
`lean/Sheaf` found no general word-length declaration. Searching the item id
in WeilConjectures found no declaration. DAG concept and name searches found
statements using word lengths but no definition node for this notion.
`tools/blueprint_refs.py search 'word length'` found zero blueprint nodes.
The new node includes the search-tool outputs verbatim in `mathlib_searches`.

Source: read the author-hosted Cashen PDF, version 31 October 2023,
https://www.mat.univie.ac.at/~cashen/Notes_on_Coxeter_groups.pdf,
Chapter 4, Lemma 4.0.5, printed p.118, and Lemma 4.0.14(2), pp.120–121.
The deletion argument is the one-sided specialization with the right subgroup
trivial, as the DAG's complete elementary proof specifies. The theorem's
docstring retains all five proof steps, including all three locations of the
pair of deleted positions. No theorem is proved in this stage.

Validation: both delivery modules compiled separately through `scompile.py`,
including the sibling import, with no errors or unexpected warnings.

## New nodes

`def-sfb-generator-word-length` defines the minimum positive-word length for
an arbitrary indexed monoid alphabet, using `List` products and `sInf` on ℕ.
It also provides the same construction on a subset alphabet, without a second
definition. This is the minimal-word notion used in Cashen Lemma 4.0.5; totalizing
by zero outside the represented submonoid has no effect on this consumer.
The node requires no new group-theoretic axiom or existence theorem. The searches
above show that Mathlib only supplies the Coxeter-presentation specialization,
not this definition for a bare alphabet. DAG searches found no existing owning
node. The item's only change besides `lean` is adding this definition dependency.

## Second reading by NY

Author's second pass, not an independent review (this dispatcher brief prohibits
starting other agents; independent review is the maintainer's delivery review).
Reopened the node and both Lean files and checked the correspondence above.
The general length definition takes the minimum over `A.length = n` and
`(A.map t).prod = g`, with no hidden finite-group assumption. Restricted words
use the subtype `J`, not an arbitrary length function. The deletion indices
are ordered and bounded in the original list and deleted from right to left.
The two conclusions retain all quantifiers and both length formulas. The
subgroup closure agrees with the word description because the letters are
involutions. The only potential mismatch considered was a specialized Coxeter
length API; it was avoided by the supplied general definition. No mismatch
was found and no statement correction was made.
