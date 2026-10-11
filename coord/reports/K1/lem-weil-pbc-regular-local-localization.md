## Worker report

The module `lean/Sheaf/RingTheory/RegularLocalLocalization.lean` states that for a commutative ring `R` with an `IsRegularLocalRing R` instance and a prime ideal `p`, the localization `Localization.AtPrime p` is regular local and `R` is regular (`IsRegularRing R`). The first conclusion conjunct renders the assertion about `R_p`; the second renders the consequence that every prime localization is regular local. The binders `{R : Type u}`, `[CommRing R]`, `[IsRegularLocalRing R]`, `(p : Ideal R)`, and `[p.IsPrime]` render exactly the ring, regular-local, and prime hypotheses. The proof is `sorry` as required for stage 2.

Dependency declarations used: `IsRegularLocalRing` and `IsRegularRing` from `Mathlib.RingTheory.RegularLocalRing.Defs`; `Localization.AtPrime` from `Mathlib.RingTheory.Localization.AtPrime.Basic`. These are the recorded Mathlib declarations for `def-weil-regular-scheme` and `def-weil-pbc-localization-at-prime`.

Edge cases checked: arbitrary universe `u`; arbitrary prime ideal (including maximal and zero primes when prime); no nonzero or finite-dimensional hypothesis is added. The conjunction permits the same statement when `R` is a field or has dimension zero.

Searches run on 2026-10-11:

- `msearch.py leansearch`, query "localization of a regular local ring at a prime ideal is regular local": unavailable (Internal Server Error); no verdict inferred.
- `msearch.py leanfinder`, query "localization of a regular local ring at a prime ideal is a regular local ring": eight hits, including local-ring localization and regular sequences; none states regular-local preservation.
- `msearch.py loogle`, query "IsRegularLocalRing, Localization.AtPrime": four hits. The class field assumes `IsRegularRing R` already; the polynomial theorem concerns a different ring and primes over the maximal ideal. Neither matches.
- `msearch.py grep`, query `IsRegularLocalRing|IsRegularRing` in `RingTheory/RegularLocalRing`: definitions and the polynomial special case; no match. The pinned Mathlib Defs file explicitly lists regular-local implies regular as a TODO.
- `rg -n 'IsRegularLocalRing|IsRegularRing|regular-local-localization'` in `WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`: upstream has regular-ring localization, etale regularity and projective-dimension results, but no regular-local localization assertion. Project files cite this node in proof docstrings, and `LocalizationOfRegularRing` assumes a regular ring, so none matches.
- The final declaration name was searched in the upstream source, Mathlib and project: no existing declaration.

Source checked online because the local literature checkout is absent: [Stacks 0AFS](https://stacks.math.columbia.edu/tag/0AFS) states the prime-localization assertion; [Stacks 00OD](https://stacks.math.columbia.edu/tag/00OD) defines a regular ring as Noetherian with regular local prime localizations. No correction or disputed statement is needed. The theorem docstring carries all five DAG proof steps and their dependency names.

Independent second reading is pending; the second reader will write that section and deliver.

## Second reading by K1

I independently compared the node's objects, hypotheses, and conclusion with
`Sheaf.RingTheory.RegularLocalLocalization`.

- **Objects and hypotheses.** The node introduces a commutative ring `(R, m)`
  carrying the regular-local condition and a prime ideal `p ⊂ R`. Lean renders
  these as `{R : Type u} [CommRing R] [IsRegularLocalRing R] (p : Ideal R)
  [p.IsPrime]`. `IsRegularLocalRing R` is Mathlib's class extending
  `IsLocalRing R` and `IsNoetherianRing R`, with the maximal-ideal span
  condition, so it supplies exactly the node's regular-local hypotheses. The
  prime binder is exactly the node's prime-ideal assumption. No field,
  Noetherian, finiteness, characteristic, or universe restriction is added.
- **First conclusion.** The node's `R_p` is Mathlib's
  `Localization.AtPrime p`; Lean's first conjunct is
  `IsRegularLocalRing (Localization.AtPrime p)`, exactly the assertion that
  this localization is regular local.
- **Consequence.** The node's assertion that every prime localization of `R`
  is regular local and hence `R` is regular is rendered by the second conjunct
  `IsRegularRing R`. Mathlib defines this as Noetherianity together with
  `IsRegularLocalRing (Localization.AtPrime q)` for every prime `q`, matching
  the node's quantifiers and clause. The conjunction keeps the chosen `p`
  assertion and the all-primes consequence in the same theorem.

The theorem has no unbound variables and compiles cleanly with
`scompile.py`. Its proof remains the required `sorry`; no definition is
hollow. The docstring records all five proof steps and their dependency-node
names, with the source place and `(blueprint: lem-weil-pbc-regular-local-localization)`.

Edge cases checked: `u` is arbitrary; `p` may be any prime (including zero or
maximal when prime); fields and zero-dimensional regular local rings are
covered; no nonzero, finite-dimensional, characteristic, or nonempty-scheme
assumption is introduced. The statement also covers the maximal-prime
localization, which is consistent with the consequence.

Searches were rechecked against Mathlib's
`RingTheory/RegularLocalRing/Defs.lean`, `RingTheory/RegularLocalRing/Polynomial.lean`,
`RingTheory/Localization/AtPrime/Basic.lean`, the slopmaster2
`WeilConjectures/` tree, this repository's `lean/Sheaf`, and
`dag/lean_names_upstream.json`. LeanSearch, LeanFinder, Loogle, and grep
queries for localization preserving `IsRegularLocalRing` found only the
circular `IsRegularRing.isRegularLocalRing_localization` field and a
polynomial special case; no declaration states this theorem. Thus no existing
notion or statement supersedes the module.

No mismatch was found. The worker module and node statement were left
unchanged.
