## Worker report

The module `Sheaf.GroupTheory.OrderedBlockPermutationSign` states
`Equiv.Perm.sign_orderedBlocks`, with its entire proof postponed by `sorry`.
There are no new definitions, helper theorems, dependency modules, or statement corrections.
The accepted stage-1 statement and split are unchanged; the node copy changes only `lean`.
The earlier worker's stale stage-1 assignment diagnosis does not apply to this stage-2
assignment: the node has no Lean record, occurs in the stage-2 queue, and the maintenance
handoff at the beginning of `coord/brief-stage2.md` explicitly authorizes this work.

Hypothesis and clause correspondence:

- Nonnegative integers `q` and `s` and `s ≤ q` are `{q s : ℕ}` and `(hs : s ≤ q)`.
  Natural numbers represent exactly the nonnegative integers in the statement.
- The source's ordered set `[q] = {1, …, q}` is represented by `Fin q` via the
  order-preserving relabelling `i ↦ i.val + 1`. This also represents `[0]` by the empty type.
  Permutations and their signs are preserved under this relabelling, which carries
  transpositions to transpositions. The formula retains the one-based numerical labels.
- The subsets are `(T I : Finset (Fin q))`. Every subset of this finite ambient set is
  represented. Their common size is `(hT : T.card = s)` and `(hI : I.card = s)`.
- Their increasing lists are `T.orderEmbOfFin hT` and `I.orderEmbOfFin hI` from
  `Fin s`. Mathlib defines these as increasing bijections onto the respective finite sets.
- The complements are `Tᶜ` and `Iᶜ`, enumerated increasingly by `orderEmbOfFin` from
  `Fin (q - s)`. The inline proofs `by simp [Finset.card_compl, hT]` and its `hI`
  counterpart establish their cardinalities using existing Mathlib theorems; they do not
  introduce new postponed claims or assumptions.
- The permutation of the ambient set is `(σ : Equiv.Perm (Fin q))` and the condition
  `σ(T) = I` is exactly `(hσ : T.image σ = I)`.
- The source's induced permutations are `(α : Equiv.Perm (Fin s))` and
  `(β : Equiv.Perm (Fin (q - s)))`. The two defining equations are binders `hα` and
  `hβ`, universally quantified over their respective positions. Thus these are precisely
  the induced permutations, not arbitrary unrelated maps. The increasing bijections and
  `hσ` uniquely determine them; the complementary equation follows the complement image
  equality supplied by the bijection `σ`. Presenting uniquely specified objects with
  their defining equations is equivalent to the source's “define α and β by” phrasing.
- The sign is the same Mathlib homomorphism `Equiv.Perm.sign` identified in the determinant
  dependency, with its integer units coerced to `ℤ`. The exponent is exactly
  `(∑ i ∈ I, (i.val + 1)) + ∑ t ∈ T, (t.val + 1)`; the conclusion is equality in `ℤ`
  with the two induced signs multiplied in the source's order.
- All empty cases are included by these same binders, without nonemptiness assumptions.
  For `s = 0`, the subset permutations are the unique permutation of `Fin 0` and both
  increasing complement lists enumerate the full set. For `s = q`, the complementary
  permutations are empty and the exponent is `q(q + 1)`. For `q = 0`, necessarily `s = 0`,
  the sums are empty and every sign is one. Mathlib's sign is a homomorphism, so the
  unique empty permutation has sign one without a separate convention or extra conclusion.

Dependency declarations read and used:

- `def-weil-pbc-matrix-determinant`: `Mathlib.LinearAlgebra.Matrix.Determinant.Basic`,
  `Matrix.det` and `Matrix.det_apply`, whose sign is `Equiv.Perm.sign` in
  `Mathlib.GroupTheory.Perm.Sign`. Read the full definitions and docstrings, as well as
  `sign_swap`, `sign_one`, and invariance under conjugating by a bijection. The determinant
  module is a public statement-dependency import; this theorem uses its permutation sign.
- Proof dependency `lem-sfb-permutation-sign-inversion-product` is a Mathlib leaf, with
  `Equiv.Perm.sign_eq_prod_prod_Ioi` in `Mathlib.GroupTheory.Perm.Fin` (lines 508–511).
  Its full signature was read, including the integer-unit codomain. Its module is a plain
  proof import. The module docstring transcribes the complete four-step accepted proof.
- `Mathlib.Data.Finset.Sort`, `Finset.orderEmbOfFin`, `Finset.orderIsoOfFin`, their
  full definitions and docstrings, and `Finset.range_orderEmbOfFin` were read to check that
  the enumerations are exhaustive and increasing, not arbitrary injections.

Searches for an existing exact statement (all through the prescribed `msearch.py` where
applicable):

- LeanFinder: “The sign of a permutation mapping an ordered subset T onto I equals minus
  one to the sums of T and I times the signs of its induced permutations on the subsets
  and complements”. Eight hits included `sign_subtypeCongr`, `sign_sumCongr`, and
  `sign_eq_prod_prod_Ioi`; none gives the ordered-subset sum parity formula.
- Loogle: `Equiv.Perm.sign, "sumCongr"`. One hit, `Equiv.Perm.sign_sumCongr`.
  Its full signature and source were read: it only handles permutations on a fixed
  disjoint union, with no ordered-subset shuffle factor.
- Mathlib grep: `sign.*(sumCongr|shuffle|subtype|restrict)` in `GroupTheory/Perm`.
  Six hits concerning subtype restrictions and signs; none states this formula.
- LeanSearch: “Sign of a permutation mapping ordered complementary subsets with factor
  minus one to sums of selected indices”. Eight hits on signs and alternating maps;
  no exact statement. `sign_subtypeCongr` was also read in the source: it likewise lacks
  the numerical shuffle factor between different subsets.
- Project `rg`: `ordered.block|permutation.sign|sign.*(sumCongr|shuffle)|` followed by
  the item id in `lean/WeilConjectures` and `lean/Sheaf`; the hits concern Koszul signs,
  simplicial shuffles, Cech sorting, and geometric block permutations, not this theorem.
  Both `rg` and the requested `grep -rn` for the item id in `lean/WeilConjectures` found
  no declaration. A further exact-name search for `sign_ordered` and `orderedBlock`
  in both project roots and Mathlib's permutation directory found no declaration.

Source check: read Stacks `more-algebra.tex`, lines 1325–1353 (Tag 07Z7). The proof
is omitted with an expansion hint; this permutation calculation is correctly attributed
as agent-supplied, rather than quoted as a theorem of Stacks.

Verification: prescribed `scompile.py` compiled both its sandbox representation and the
actual library module cleanly in approximately 1.1 and 1.2 seconds, respectively. No
warnings or errors were printed. An independent finite enumeration checked all 4,283
cases for `0 ≤ q ≤ 5`, all permutations and subsets, using inversion counts for every
sign and the exact one-based exponent above. This includes every empty/full block case.
There is no statement dispute or node fault.

The maintainer performs the independent review, as required by this direct-delivery brief.

## Second reading by Q139

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
