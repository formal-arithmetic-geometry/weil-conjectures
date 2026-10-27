## Worker report

The module `Sheaf.GroupTheory.StrongExchangeSubwordExtension` states
`Subgroup.exists_reduced_subword_extension_of_strong_exchange`. Its sole theorem has
proof `sorry`; it introduces no definitions, axioms, helper theorems or new nodes.
The accepted stage-1 statement, dependencies and six-step proof are unchanged.
The inherited BLOCKED ending concerned the accepted Q08 stage-1 split. The current
node has no Lean binding and is in the stage-2 queue; brief-stage2 section 0 explicitly
authorizes this handoff. There is no released repair note for the item.

Hypothesis and conclusion correspondence:

1. The finite-dimensional real vector space is `V : Type u`, with `AddCommGroup V`,
   `Module ℝ V`, and `FiniteDimensional ℝ V`. The universe is explicit and arbitrary.
2. The actual real linear subgroup is
   `G : Subgroup (LinearMap.GeneralLinearGroup ℝ V)`. Mathlib defines this general
   linear group as units of the real linear endomorphism ring; these are precisely
   invertible real linear maps. No Coxeter system or root datum is assumed.
3. The generating set is `S : Set G`. The hypothesis `hS` says for every member
   `s` that `s ≠ 1` and `s ^ 2 = 1`, exactly the nonidentity and involution conditions.
   A word is a `List S`; mapping `Subtype.val` regards its letters as elements of
   `G`, and `List.prod` multiplies them in their given order.
4. `hlength` says `IsLeast {n | ∃ a : List S, (a.map Subtype.val).prod = g ∧
   a.length = n} (ℓ g)` for every `g`. Its membership clause gives a word for every
   group element, so it includes exactly the generation hypothesis. Its minimality
   clause says that `ℓ g` is the least number of letters. This specifies the named
   length function uniquely, rather than assuming a length with extra properties.
   Existence of this specification follows from the node's generation condition
   and well-ordering of the natural numbers. No Coxeter length is substituted.
   Reducedness is expanded as equality of this length and the word's letter count.
5. The node's conjugate set `T` is expanded in `hexchange` as
   `∃ (h : G) (s : S), t = h⁻¹ * s.val * h`. Thus `t` ranges over precisely `T`.
6. `hexchange` quantifies over every list `a`, including nonreduced and empty
   lists, and uses the node's non-strict inequality
   `ℓ ((a.map Subtype.val).prod * t) ≤ ℓ (a.map Subtype.val).prod`.
   Its conclusion `1 ≤ a.length` renders `n ≥ 1`, and `j : Fin a.length`
   supplies a valid deletion position. The equality uses `a.eraseIdx j.val`,
   which removes that position and retains every other letter in its original
   order. No reducedness or parity hypothesis is added to exchange.
7. The full word is `b : List S`; its number of letters is `q = b.length`.
   Using a list instead of separately binding `q` covers every nonnegative `q`
   and every `q`-letter word. `hv` fixes its product to `v` and `hb` says it is reduced.
8. `u v : G` and `huv : u ≠ v` render the distinct group elements.
9. `hsub` gives an actual list `a : List S` with `a.Sublist b`, product `u`, and
   `a.length = ℓ u`. Mathlib's `List.Sublist` permits arbitrary omissions and
   keeps the original order, including when letters repeat and when `a` is empty.
10. The witnesses `I : Finset (Fin b.length)` and `r : Fin b.length` are respectively
    a subset of all positions and another position, with `r ∉ I`.
    Positions are numbered from zero; adding one identifies them increasingly
    with the source's positions `1,...,q`. This changes neither order nor selection.
11. `I.sort (· ≤ ·)` lists exactly the selected positions in increasing order.
    Mapping `fun i ↦ (b.get i).val` produces precisely the selected word in `G`.
    Its product is asserted to be `u`, and `I.card = ℓ u` says this word is reduced:
    `Finset.length_sort` and `List.length_map` identify its letter count with `I.card`.
12. Applying the identical construction to `insert r I` selects exactly
    `I ∪ {r}`, in increasing order. The next equality says that the length of
    its product is `(insert r I).card`, so this word is reduced too.
    The last equality makes its letter count `ℓ u + 1`. Both of the node's
    asserted lengths are therefore explicit, without naming a different extension.

The only statement dependency is `def-weil-vector-space-dimension`. Its Mathlib
binding is `Module.finrank` in `Mathlib.LinearAlgebra.Dimension.Finrank`, imported
publicly. I read its complete signature and docstring (lines 48--63), and the
finite-basis cardinality statement `Module.finrank_eq_card_basis` in
`Mathlib.LinearAlgebra.Dimension.StrongRankCondition` (lines 449--453). The node
does not use a numerical dimension, only finite-dimensionality, so no artificial
`finrank` bound or equality appears in the theorem. `FiniteDimensional` is the
existing Mathlib abbreviation in `Mathlib.LinearAlgebra.FiniteDimensional.Defs`,
read at lines 73--76. The remaining interfaces are Mathlib's existing
`LinearMap.GeneralLinearGroup`, `Subgroup`, `List.Sublist`, `List.eraseIdx`,
`List.prod`, `IsLeast`, `Finset.sort`, and `Finset.card`; no missing notion needs
a new definition node. In particular, generation and least word length are stated
directly with lists, natural numbers and `IsLeast`, rather than creating a parallel
API for Coxeter words.

Source read: Björner--Brenti, *Combinatorics of Coxeter Groups*, Lemma 2.2.1 and
proof, printed pages 33--34 (PDF pages 41--42, zero-based), including the remark
that deletion may precede the first originally omitted position, at
https://sites.math.washington.edu/~billey/classes/reflection.groups/references/EntireBook.pdf.
The node deliberately extracts the position-insertion argument and displays the
exchange assumptions it actually uses; I preserve this accepted formulation.
I also read the latest blueprint's `sk-thm-sf-ctf-stability/_section.md` and
`sk-thm-sf-ctf-stability-direct-images.proof.md`, clause (3), which is the ancestor
place recorded in the accepted split. The declaration docstring carries all six
steps of the node's minimal-last-omission proof, including both deletion cases.

Edge cases checked before writing:

- For `b = []`, every sublist is empty. The two product equalities force `u = v = 1`,
  contradicting `huv`; no impossible `Fin 0` witness is demanded from consistent data.
- If `S` is empty, every `List S` is empty and `hlength` forces `G` to be trivial.
  The distinctness hypothesis cannot hold. No `Nonempty S` assumption was introduced.
- If the selected subword is empty but `b` is nonempty, it represents `1` and
  has length zero. Insertion of a generator is covered; no positive-length
  assumption on `u` or on the original selection is present.
- Dimension zero gives the trivial linear group and hence the same vacuous
  distinctness case; no `Nontrivial V` or positive dimension was added.
- In the permutation realization of S3, write `s=(12)`, `t=(23)`, `b=[s,t,s]`,
  and `u=s`. Selecting the last position and then inserting the middle one gives
  the reduced extension `[t,s]`. Selecting the first position and inserting the
  last would give `[s,s]`, which is not reduced: the conclusion correctly asks
  for some selection `I`, not every initial selection. For `u=1`, the empty
  selection and any one position give the allowed one-letter extension.

Searches actually run using `msearch.py Q112 lem-sfb-exchange-reduced-subword-extension`:

- LeanFinder: `In a group generated by involutions with strong exchange, a proper
  reduced subword of a reduced word extends by one inserted letter`. Eight hits,
  including free-group reduction results and Coxeter reduced prefixes/suffixes;
  none states the insertion result.
- Loogle: `CoxeterSystem.IsReduced`. Twelve hits. I read `CoxeterSystem.IsReduced`
  and `length` at Length.lean:75--82, plus `.take` and `.drop` at 231--237.
  These require an actual Coxeter system and retain only a prefix or suffix.
  They do not supply this conclusion under the given explicit exchange property.
- Mathlib grep: `wordLength|WordLength|wordMetric|word metric`, under `GroupTheory`:
  zero hits, so there is no matching general generating-set word-length interface.
- LeanSearch: `A reduced subword of a reduced word can be extended by one letter
  under strong exchange`. Eight hits, again free-group reduction and Coxeter
  prefix/suffix facts. The free-group notion means absence of adjacent cancellation;
  it is not minimal length in this specified linear subgroup.
- Mathlib grep: `subword|Subword|exchange|deletion`, under `GroupTheory/Coxeter`:
  zero hits. No existing theorem exactly matches the node.
- Direct `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `wordLength|WordLength|strong_exchange|strongExchange|subword_extension|subword.*inser|inser.*subword`
  found no matches. A broader reduced-word search found only unrelated six-functor
  composition words. The requested search for the exact node id in
  `lean/WeilConjectures` also found no declaration. No source declaration was copied.

There is no statement correction and no disputed statement. The server compiler
accepted the module both in the sandbox and at its intended library module path.
All universes and variables are explicit; `autoImplicit` is disabled.

## Second reading by Q112

I performed a separate second pass in this worker session, with the JSON statement
and the completed Lean declaration open. The dispatch forbids starting another
agent, so this paragraph does not claim a second person's review; the maintainer
performs the independent delivery review.

Reading the conclusion first, the selected positions are genuine positions of
the fixed word and their sort uses the natural increasing order. The result does
not merely assert an unrelated word of length one greater. The same `I` represents
`u`, and `insert r I` is the required one-position extension. The two cardinality
equalities count letters rather than distinct generator values, so repeated
letters are handled correctly. Checking the hypotheses backward, `hsub` contains
reducedness as well as containment and the product equality; `hb` is reducedness
of the full word and `huv` retains strict properness. The exchange assumption uses
right multiplication, the correct conjugation orientation, a non-strict length
inequality, and all words. Its `Fin a.length` deletion witness does not silently
permit deletion outside the list, while `1 ≤ a.length` preserves the source's
explicit nonempty conclusion. Finally, `hlength` contains attainment and the
lower-bound property, which together express exactly the minimum specified in
the node and supply generation without adding a hypothesis about a root system.
The ambient group is the actual subgroup of invertible real linear maps, not an
abstract replacement. The finite-dimensional hypothesis covers dimension zero
and every universe. No mismatch required changing the accepted node. The only
change during the second pass was to disable automatic implicit variables
explicitly; this leaves the signature unchanged. The existing compact-object
example module is withdrawn in the current clone; the module header follows
the current mandatory module-mode conventions in brief-stage2 section 4.
