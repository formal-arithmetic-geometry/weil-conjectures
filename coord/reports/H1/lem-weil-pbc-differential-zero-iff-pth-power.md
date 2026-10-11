## Worker report

The module `Sheaf.RingTheory.KaehlerDifferentialZeroIffPow` states
`KaehlerDifferential.D_eq_zero_iff_exists_pow_of_perfectField`; its only proof is `sorry`.
No definitions, new nodes, dependency repairs, or statement corrections were needed.

The correspondence with the node, hypothesis by hypothesis and clause by clause:

- The prime number is `(p : ℕ) [Fact p.Prime]`.
- The base field is `(k : Type u) [Field k]`.
- Characteristic p is `[CharP k p]`. In a field and for prime p this is equivalent to
  the node's `p • 1 = 0`: the characteristic divides p and cannot be 1.
- Perfection is `[PerfectField k]`. Although Mathlib defines this by separability of
  irreducible polynomials, in characteristic p it is equivalent to every element being
  a p-th power. `PerfectField.toPerfectRing` supplies the forward conversion;
  `PerfectRing.toPerfectField` supplies the reverse conversion (Frobenius is injective
  in a field, so surjectivity implies bijectivity).
- The extension field is `(K : Type v) [Field K] [Algebra k K]`.
- The universal derivation is `KaehlerDifferential.D k K`; its codomain is exactly
  `KaehlerDifferential k K`, not an arbitrary differential module or derivation.
- The arbitrary element is `(a : K)`.
- Vanishing of its differential is `D k K a = 0`.
- “If and only if a = b^p for some b in K” is `↔ ∃ b : K, a = b ^ p`.
- The parenthetical example k = F_p is illustrative, not another hypothesis or conclusion.
  The declaration includes it since F_p has characteristic p and is perfect.

Dependency declarations read and used:
`def-pc-field-extension` is the Mathlib leaf `Algebra` in
`Mathlib.Algebra.Algebra.Defs`: fields with an algebra structure encode the ring map.
`def-weil-pbc-kahler-differentials` is the Mathlib leaf `KaehlerDifferential` in
`Mathlib.RingTheory.Kaehler.Basic`, together with `KaehlerDifferential.D` and
`KaehlerDifferential.linearMapEquivDerivation`; their signatures and docstrings were read.
The last supplies precisely the universal property, with no need for a private definition.
Both direct imports are used: Kähler differentials and perfect fields respectively.

Edge cases checked before writing: a = 0 and a = 1 have p-th roots and zero differential;
K = k and algebraic extensions are included; arbitrary transcendence degree and infinite
extensions are included (no finite-generation or finiteness binder). The imperfect extension
F_p(t)/F_p is included: t is neither a p-th power nor killed by d, while t^p is killed.
The two independent explicit universes impose no relative size condition on k and K.
The prime assumption excludes p = 0 and p = 1, as does the node. No zero ring is admitted
by the node's field assumption. No statement fault or dispute found.

Source check: the local Stacks TeX is not present on this machine, so the statement of
[Stacks Tag 031W](https://stacks.math.columbia.edu/tag/031W) was opened directly. It states
exactly the equivalence for any extension of a perfect field of positive characteristic.
The docstring records all four steps of the node's p-basis proof, including its named
proof dependencies; this is the node's alternative proof, not an assertion that 031W
itself uses p-bases.

Searches for an existing statement:

- `msearch.py ... leanfinder "Over a perfect field of characteristic p the Kahler
  differential of a field element vanishes iff it is a pth power"`: eight hits, concerning
  perfect closures and characteristic-zero differential fields; no matching theorem.
- `msearch.py ... loogle "KaehlerDifferential.D, PerfectField"`: zero hits.
- `msearch.py ... grep "PerfectField|PerfectRing|CharP|frobenius" RingTheory/Kaehler`:
  zero hits.
- `msearch.py ... leansearch "Kahler differential zero iff pth power over perfect field"`:
  unavailable (Internal Server Error); no verdict from this unavailable service.
- `rg` for `KaehlerDifferential|differential-zero-iff-pth-power` in the upstream
  `WeilConjectures` and project `lean/Sheaf`: hits on differential modules, Cartier equality,
  and unramifiedness criteria, none on this equivalence.
- `grep -rn` for the item id in upstream `WeilConjectures`: no hits.
- `rg` for the item id and `D_eq_zero_iff` in `dag/lean_names_upstream.json`: no hits.
- `rg` for the chosen full theorem suffix in Mathlib, upstream `WeilConjectures`, project
  `lean/Sheaf`, and `dag/lean_names_upstream.json`: no existing declaration with this name.

Server compilation via `scompile.py`: clean, exit code 0, 1.4 seconds.

## Second reading by H1

I independently read the node, its Stacks source (Algebra, Tag 031W), and the Lean
module. The correspondence is as follows.

- Prime: the node's prime p is `(p : ℕ) [Fact p.Prime]`.
- Perfect base field: the node's field k, with characteristic p and every element a
  p-th power, is `(k : Type u) [Field k] [CharP k p] [PerfectField k]`. For a field
  and prime p, `CharP k p` is equivalent to `p • (1 : k) = 0`; `PerfectField k`
  gives the stated perfection in characteristic p.
- Extension: the node's field extension K/k is `(K : Type v) [Field K]
  [Algebra k K]`, with no finiteness or algebraicity restriction.
- Differential: the node's universal k-derivation `d : K → Ω_{K/k}` is
  `KaehlerDifferential.D k K`.
- Element and conclusion: `(a : K)` and
  `D k K a = 0 ↔ ∃ b : K, a = b ^ p`, with the same quantifier order.

The empty-index and zero-element cases are covered: no p-basis index is assumed,
and `a = 0` and `a = 1` have the expected roots. The extension may be trivial,
algebraic, transcendental, finite, or infinite. Fields exclude the zero ring, and
the prime hypothesis excludes p = 0, 1. Universes `u` and `v` are independent.

The Mathlib and project searches in the worker report were repeated with
`msearch.py` (`leanfinder`, `loogle`, and `leansearch`), `rg` in Mathlib,
`WeilConjectures`, and `lean/Sheaf`; no existing theorem states this equivalence.
The dependency declarations are Mathlib's `Algebra` encoding of a field extension
and `KaehlerDifferential`/`KaehlerDifferential.D`; neither is a private duplicate.

No statement or dependency mismatch was found, and compilation with `scompile.py`
is clean. I corrected the worker report's stray claim that the illustrative k = F_p
example was part of the declaration: it is only explanatory prose in the node and
is not a theorem binder or conclusion. The module and node statement otherwise
remain unchanged.
