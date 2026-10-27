## Worker report

The module `Sheaf.GroupTheory.FinitePGroupNormalIndex` states
`Subgroup.exists_normal_index_prime_of_card_eq_prime_pow`. Its only proof is `sorry`;
no definitions or auxiliary statements are introduced. The node is unchanged except for `lean`.

The statement matches the node hypothesis by hypothesis and clause by clause:

- The group is `(P : Type u) [Group P]`, with arbitrary explicitly declared universe `u`.
- Its underlying set is finite: `[Finite P]`. The statement dependency
  `def-sfb-finite-infinite-set` is the Mathlib leaf `Set.Finite`, in
  `Mathlib.Data.Finite.Defs`. That predicate is defined as finiteness of the subtype.
  Finiteness of the whole underlying set is equivalently `Finite P`, as also recorded by
  `Set.finite_univ_iff` in `Mathlib.Data.Set.Finite.Basic`. This uses the existing
  Mathlib notion, with no replacement predicate or extra structure.
- The prime natural number is `(p : ℕ)` with `(hp : p.Prime)`, using `Nat.Prime`
  from `Mathlib.Data.Nat.Prime.Defs`.
- The integer exponent at least one is `(a : ℕ)` with `(ha : 1 ≤ a)`. Positive
  integers are precisely positive natural numbers; this encoding excludes no permitted
  exponent and does not allow a negative exponent or the zero case.
- The exact order hypothesis is `(hcard : Nat.card P = p ^ a)`.
- The same subgroup in both conclusions is `∃ H : Subgroup P`.
- The conjugation equality for every group element is `H.Normal`, Mathlib's
  `Subgroup.Normal` in `Mathlib.Algebra.Group.Subgroup.Defs` (publicly available through
  `Mathlib.GroupTheory.Index`). Its field gives `g * h * g⁻¹ ∈ H` for every `h ∈ H`
  and every `g`. This gives `gHg⁻¹ ⊆ H`; using `g⁻¹` gives the reverse inclusion,
  hence exactly the equality in the node, with no additional normality requirement.
- The second clause is `H.index = p`; `Subgroup.index` in `Mathlib.GroupTheory.Index`
  is `Nat.card (P ⧸ H)`, the number of left cosets. Finiteness of `P` ensures this is
  the actual finite count rather than the infinite-index zero convention.

The proof dependencies are all Mathlib leaves. Their complete signatures and surrounding
source were read; their modules are imported privately for stage 3:

- `lem-sfb-finite-subgroup-prime-power-order`:
  `Sylow.exists_subgroup_card_pow_prime`, `Mathlib.GroupTheory.Sylow`, assumes `[Finite G]`,
  `[Fact p.Prime]`, and `p ^ n ∣ Nat.card G`; returns a subgroup of order `p ^ n`.
- `lem-sfb-surjective-subgroup-image-index`:
  `Subgroup.index_map_dvd` and `Subgroup.card_mul_index`, `Mathlib.GroupTheory.Index`.
  The latter gives `Nat.card H * H.index = Nat.card G`; the former is the other
  clause of the dependency and is not needed beyond the identity-surjection specialization.
- `lem-sfb-least-prime-index-normal`:
  `Subgroup.normal_of_index_eq_minFac_card`, `Mathlib.GroupTheory.IndexNormal`, assumes
  `H.index = (Nat.card G).minFac` and returns `H.Normal`.

The docstring contains all four steps of the accepted proof: choose order `p^(a-1)` by
Sylow, compute index using order times index and positive-factor cancellation, identify the
least prime divisor, and apply normality at least-prime index. The source context was read
in `literature/stacks-project/more-algebra.tex`, Tag 09F8, `lemma-special-case`, normal-extension
filtration paragraph following Tag 09EE. As the node records, the group-theoretic argument
is agent-supplied, and the Stacks text supplies its application rather than this precise lemma.

Edge cases checked before drafting: for `a = 1`, the trivial subgroup is normal of index `p`;
`p = 2` is included; the trivial ambient group cannot satisfy the positive prime-power order
hypothesis; `a = 0` is correctly excluded (otherwise the assertion fails for the trivial group).
The claim includes noncyclic and nonabelian groups, for example elementary abelian groups and
groups of order eight. No cyclicity, commutativity or choice of enumeration is assumed.
No statement correction or disputed statement is needed, and no new nodes or dependency
modules are needed.

Searches performed with the prescribed `msearch.py` wrapper:

- LeanFinder: `Every nontrivial finite p-group has a normal subgroup of index p`.
  Eight hits, including `IsPGroup.toSylow`, `IsPGroup.bot_lt_center`,
  `IsPGroup.center_nontrivial`, `IsPGroup.index`, and
  `Sylow.exists_subgroup_card_pow_prime_of_le_card`; no exact combined assertion.
- Loogle: `IsPGroup, Subgroup.index`. Seven hits, including the online
  `IsPGroup.isCoatom_iff_index_eq_prime` characterization; it is absent from the pinned
  local Mathlib source and does not directly state this existence-and-normality theorem.
- Mathlib grep, restricted to `GroupTheory`:
  `exists.*normal.*index|exists.*index.*prime|isCoatom_iff_index_eq_prime|normal_of_index_eq_minFac_card`.
  Only `Subgroup.normal_of_index_eq_minFac_card` matched, a criterion for an already
  supplied subgroup rather than existence.
- `rg` in both `lean/WeilConjectures` and `lean/Sheaf` for
  `normal.*index.*[pP]|exists.*normal.*index|finite.p.group|lem-sfb-finite-p-group-normal-index-p`:
  contextual mentions of wild p-group kernels and unrelated normalizations, no declaration
  of this assertion. The required recursive grep for the exact node id in
  `lean/WeilConjectures` returned no match.
- Declaration-name search in `dag/lean_names_upstream.json`, the project source trees,
  and Mathlib `GroupTheory` found no existing declaration with the planned name or its
  candidate variants. The read node's own recorded searches likewise found no exact match.

Validation uses `scompile.py` only. The initial module-mode check diagnosed `Nat.Prime` as
privately imported; adding its direct public definition import repairs the visibility.
The delivered file is compiled independently against the published server library, with all
variables and universes explicit, and no diagnostic commands left in the module.

## Second reading by Q44

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
