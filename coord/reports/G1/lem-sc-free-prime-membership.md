## Worker report

The module `Sheaf.RingTheory.FreePrimeMembership` states
`Module.free_prime_mem_localized_iff`, with a single `sorry` and no definitions or proofs.
It renders both the vector membership equivalence and the node's equivalent scalar
coordinate assertion as a conjunction. No node correction or extra notion is needed.

Hypothesis and clause correspondence:

- Commutative ring R: `{R : Type u} [CommRing R]`, with explicit universe `u`.
- Finite free module F = R^n: `(n : ℕ)` and the standard Mathlib module `Fin n → R`.
- Section/vector s = (s_1,...,s_n): `(s : Fin n → R)`, with coordinate `s i`.
- Prime ideal p: `(p : Ideal R) [p.IsPrime]`; no maximality or domain assumption.
- Multiplicative subset S = R minus p: `p.primeCompl`.
- Localized module F_p = S^{-1}F: `LocalizedModule p.primeCompl (Fin n → R)`.
- Canonical localization map s ↦ s/1:
  `LocalizedModule.mkLinearMap p.primeCompl (Fin n → R) s`.
- Localized ring R_p: `Localization.AtPrime p`.
- Ideal pR_p: `Ideal.map (algebraMap R (Localization.AtPrime p)) p`.
- Submodule pF_p: this extended ideal acting on the top R_p-submodule of F_p.
  This uses the localized-ring module structure, as in the already recorded citer
  `Module.prime_mem_localized_iff`, rather than identifying F_p with a private copy of R_p^n.
- Vector equivalence: the first conjunct says s/1 belongs to pF_p iff
  `s ∈ p • (⊤ : Submodule R (Fin n → R))` (the submodule pF).
- Each coordinate equivalence: the second conjunct quantifies `∀ i : Fin n` and says
  `algebraMap R (Localization.AtPrime p) (s i) ∈ Ideal.map ... p ↔ s i ∈ p`.
  Ring fractions with denominator 1 are rendered by the canonical algebra map.

Dependency declarations read and used:

- `def-weil-pbc-module-localization` is a Mathlib leaf. Its `mathlib_match` is
  `LocalizedModule` in `Mathlib.Algebra.Module.LocalizedModule.Basic`; its full construction,
  `LocalizedModule.mk`, `LocalizedModule.mk_eq`, and `LocalizedModule.mkLinearMap` were read.
  The last map has type `M →ₗ[R] LocalizedModule S M` and sends m to m/1.
- `def-weil-pbc-localization-at-prime` is a Mathlib leaf. Its match includes
  `Localization.AtPrime` in `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Ideal.ResidueField` in `Mathlib.RingTheory.LocalRing.ResidueField.Ideal`, and
  `Ideal.Fiber` in `Mathlib.RingTheory.LocalRing.ResidueField.Fiber`.
  All three recorded definitions and their docstrings were read; only the first is
  required here. It abbreviates `Localization p.primeCompl`. No residue-field or
  fibre-ring clause is part of this item's statement, so those modules are not imported.

Edge cases checked before writing: n = 0 gives the zero module and a vacuous coordinate
clause; s = 0 belongs on both sides. A zero ring has no prime ideal, so the prime hypothesis
correctly rules it out without a separate nontriviality assumption. For p = 0 in a domain,
the assertion is injectivity into the fraction localization. Zero divisors in R are
allowed: clearing denominators and using primality is sufficient. There is no characteristic
restriction. Finite n is essential for the finite coordinate/common-denominator argument.

Searches made on 2026-10-11 (via `/home/ubuntu/weil-launcher/msearch.py`):

- LeanFinder query: "For a finite free module R^n, the image of a vector in its localization
  at a prime ideal p belongs to p times the localized module if and only if the vector
  belongs to p times R^n". Eight hits: `Submodule.mem_of_isLocalized_span`,
  `Submodule.mem_of_localization_maximal`, `Submodule.mem_localized'`,
  `IsLocalization.mem_coeSubmodule`, `IsLocalization.mk'_mem_map_algebraMap_iff`,
  `IsLocalization.mk'_mem_iff`, `Submodule.mem_localized₀`, and
  `IsLocalization.mem_localizationLocalizationSubmodule`. None states this finite-free
  vector equivalence together with its coordinate criterion.
- Loogle query: `IsLocalization.mem_map_algebraMap_iff, Submodule.smul`; zero hits.
- Mathlib grep query: `mem_map_algebraMap_iff|mem_localized|prime.*membership`, restricted
  to `RingTheory/Localization`: eleven hits, general ideal-localization facts, no exact match.
- LeanSearch query: "finite free module prime ideal membership detected after localization";
  service unavailable (Internal Server Error), recorded as unavailable rather than no match.
- `rg` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json` for
  `prime.*membership|free.*prime|mem_map_algebraMap_iff`: general localization uses and
  finite-free-locus declarations, no exact existing statement. Search for the item id in
  `WeilConjectures` gave no hits. Search for proposed name `free_prime_mem_localized_iff`
  in Mathlib, upstream, the project's Lean, and upstream-name records gave no hits.
- Read `Sheaf.RingTheory.AffineFiniteProjectivePrimeMembership`: its theorem has the
  finite-projective generality and does not give the coordinate clause, and its docstring
  explicitly expects this finite-free item as a proof ingredient. The module here uses
  its same canonical localized-module and extended-ideal expressions.

The local Stacks checkout is absent. Source places were read from the official pages:
[00CO](https://stacks.math.columbia.edu/tag/00CO),
[07JZ](https://stacks.math.columbia.edu/tag/07JZ), and
[00NX](https://stacks.math.columbia.edu/tag/00NX).
The latter supplies the finite-free/direct-summand context; the node's scalar calculation
is the elementary prime-localization calculation, not a separately numbered assertion
on that page. The declaration docstring carries the full node proof for stage 3.

No statement dispute, missing dependency, or statement correction was found.

## Second reading by G1

I read the node statement and the module signature item by item. The objects and
hypotheses are rendered as follows: `{R : Type u} [CommRing R]` is the commutative
base ring; `(n : ℕ)` and `s : Fin n → R` are the finite free module and section;
`p : Ideal R` with `[p.IsPrime]` is the prime ideal; `p.primeCompl` is
`S = R \ p`; `LocalizedModule p.primeCompl (Fin n → R)` is `F_p`; and
`LocalizedModule.mkLinearMap ... s` is the canonical map sending `s` to `s/1`.
The first conjunct of `Module.free_prime_mem_localized_iff` is exactly
membership in the extended ideal acting on the top localized submodule iff
membership in `p • ⊤` in the original free module. The second conjunct quantifies
every `i : Fin n` and renders the node's coordinate equivalence using
`algebraMap R (Localization.AtPrime p) (s i)` for `s_i/1` and
`Ideal.map ... p` for `pR_p`. Quantifier order and both conclusion clauses agree;
the explicit universe is bound and no extra finiteness, characteristic, or
Noetherian assumptions occur. The dependency notions are the recorded
`LocalizedModule` and `Localization.AtPrime` declarations.

Edge cases remain covered: for `n = 0` the coordinate clause is vacuous and the
free module is zero; `s = 0` satisfies both sides; a zero ring has no prime ideal;
the zero prime in a domain and arbitrary characteristic are allowed. The module
compiled cleanly with `scompile.py`; no unbound variables or warnings occurred.

I repeated the existing-definition searches with LeanFinder, grep over Mathlib and
the source repository, and the proposed declaration name. LeanFinder returned only
general localization and finiteness lemmas; grep found no exact finite-free prime
membership statement; the source search found no declaration. Thus this is a new
statement module. No mismatch was found and no file or node field was changed in
the second reading.
