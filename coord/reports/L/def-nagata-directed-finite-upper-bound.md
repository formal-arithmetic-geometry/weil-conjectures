# def-nagata-directed-finite-upper-bound (L, stage 2)

## Worker report

Worker W-dub0518 for L, stage 2, item `def-nagata-directed-finite-upper-bound`. Module
`lean/Sheaf/Order/DirectedFiniteUpperBound.lean` (`Sheaf.Order.DirectedFiniteUpperBound`, sandbox
`lean/.sandbox/L/DirectedFiniteUpperBound.lean`), root namespace, import `Mathlib.Data.Finset.Sort` only.
Compiles clean (0.9 s; only the expected `declaration uses sorry` on the three theorems, lines ≤ 100).

**Defines** `directedFiniteUpperBound {I : Type u} (i₀ : I) (d : I → I → I) (r : LinearOrder I)
(F : Finset I) : I := letI : LinearOrder I := r; (F.sort (· ≤ ·)).foldl d i₀`.

Clause by clause:
- "I nonempty directed set" / "base point i_∅": the datum `i₀ : I` (witnesses nonemptiness). The order
  `≤` and directedness are not used by the definition, so the def takes no `[Preorder I]`; directedness is
  only the reason a `d` exists. They enter as `[Preorder I]` and `hd` in `le_directedFiniteUpperBound`.
- "selected common upper bound d(i,j)": the datum `d : I → I → I`. The bound property
  `i ≤ d i j ∧ j ≤ d i j` is not needed to define u, so it is the hypothesis `hd` of the lemma, not of the
  def (lead's preference; it also keeps the def free of `≤`, matching "not part of this definition").
- "auxiliary linear order ≺, unrelated to ≤": explicit structure value `r : LinearOrder I`, not an instance;
  `letI` makes it the `≤` inside the body only. In theorem statements `j ≺ i` is `r.lt j i`.
- "≺-increasing enumeration, u(F) = d(…d(d(i_∅,i_1),i_2)…,i_n), u(∅)=i_∅": `F.sort` w.r.t. r, then
  `List.foldl d i₀` (left fold: exactly the nesting of the node). Probe: on ℕ with d a b = 10a+b,
  F = {3,1,2} gives 123 for the usual order and 321 for the dual order.
- "Equivalently u(F∪{i}) = d(u F, i) if i ∉ F, j ≺ i ∀ j ∈ F": theorem `directedFiniteUpperBound_insert`
  (sorry; docstring: enumeration of insert i F is that of F followed by i, fold over l ++ [i]).
- `u(∅) = i₀`: theorem `directedFiniteUpperBound_empty` (sorry; checked true by `simp` in a probe).
- "i ≤ u(F) for i ∈ F, proved separately": theorem `le_directedFiniteUpperBound` with `[Preorder I]` and
  `hd` (sorry; docstring: induction adjoining the ≺-largest element). NOTE: this is the statement of node
  `lemma-nagata-directed-finite-upper-bound` (no `lean` yet); the lead asked for it here, so that node can
  later record it with `existing: true` rather than a second copy.

Dependencies: `def-weil-directed-colimit-abelian-groups` is a Mathlib leaf (`AddCommGroup.DirectLimit`,
directed index); only the directed-set notion is meant, rendered by `[Preorder I]` + `hd` in the lemma.
Edge cases: F = ∅ (u = i₀); I any type in any universe `u`; d arbitrary (no commutativity/associativity
assumed; order-dependence removed by r); r unrelated to ≤ (checked that `≤` in the lemma is the
Preorder's, r is never an instance outside the def body).

Searches: grep of `~/weil-conjectures-slopmaster2/WeilConjectures/` for the node id,
`directedFiniteUpperBound`, `Finset.sort`/`.sort `, `.foldl`, `UpperBound` near Finset/Nagata/directed:
no hits. `dag/lean_names_upstream.json`: no entry. Mathlib grep for `directedFiniteUpperBound` and
upper-bound defs on Finset: none; Mathlib has only existence (`Finset.exists_le`, `Directed.finset_le`),
plus the node's recorded searches (leanfinder/loogle/grep: no chosen function). Names absent.
No STATEMENT-DISPUTED; no node fault.

## Second reading by L

Independent review by R-dub0522 (reviewer sub-agent of L): FIX (lemma tag added); every clause matched; the lemma node lemma-nagata-directed-finite-upper-bound is realized by le_directedFiniteUpperBound in the same module.
