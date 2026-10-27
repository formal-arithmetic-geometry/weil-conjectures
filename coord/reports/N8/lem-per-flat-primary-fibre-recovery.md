## Worker report

The module `Sheaf.RingTheory.FlatPrimaryFibreRecovery` states
`Ideal.flat_primary_map_eq_iInf_comap_localization`, with `sorry` as its entire proof.
No definitions, helper nodes, dependency repairs or statement corrections were needed.
The item JSON changes only in `lean`.

Statement checked against the full node and the local Stacks source
`literature/stacks-project/algebra.tex`: Tags 0312 (`lemma-bourbaki`, including its
nonzerodivisor/contraction argument) and 0311 (`lemma-zero-at-ass-zero`). The node's
five-step specialization is reproduced in the theorem docstring.

Hypothesis and clause correspondence:

- Commutative rings `R` and `S`: `{R : Type u} {S : Type v} [CommRing R] [CommRing S]`.
  The universes are explicit and independent.
- Both rings Noetherian: `[IsNoetherianRing R] [IsNoetherianRing S]`.
- The specified flat ring homomorphism: `(f : R →+* S) (hf : f.Flat)`.
  This uses the recorded `RingHom.Flat`, not a separately chosen algebra action.
- The primary ideal, including properness: `(q : Ideal R) (hq : q.IsPrimary)`.
  `Ideal.isPrimary_iff` gives `q ≠ ⊤` and the product criterion with membership in
  `q.radical`. `Ideal.mem_radical_iff` uses a natural exponent; exponent zero would
  put `1` in `q` and contradict properness, so this is exactly the node's positive
  exponent condition, both for primaryness and for the displayed radical.
- The ideal `p = sqrt(q)` is `q.radical`, used directly without another parameter.
- Every prime `Q` of `S`: the index `Q : PrimeSpectrum S`, whose field `asIdeal`
  is prime by `PrimeSpectrum.isPrime`.
- The condition `f⁻¹(Q) = p`: the second intersection index
  `(_ : Q.asIdeal.comap f = q.radical)`.
- `S_Q` and its canonical map: `Localization.AtPrime Q.asIdeal` and
  `algebraMap S (Localization.AtPrime Q.asIdeal)`.
- Extension of `q` to `S`: the left side `q.map f`.
- Extension of `q` to `S_Q`: `q.map ((algebraMap S (Localization.AtPrime Q.asIdeal)).comp f)`.
  This is the extension along the actual composite `R → S → S_Q`;
  `Ideal.map_map` identifies it with extension of `qS` along the localization map.
- Contraction to `S`: `Ideal.comap` of the canonical localization map.
- Equality with the whole intersection: the displayed `q.map f = ⨅ Q, ⨅ _, ...`.
  There is no restriction to minimal or associated primes in the conclusion.
- Empty intersection: the complete lattice of ideals makes an empty indexed
  infimum `⊤`, the unit ideal of `S`. The proof-index intersection gives `⊤` for
  each `Q` outside the fibre, so the expression is precisely the intersection
  over the specified fibre, including when it is empty.
- Neither faithful flatness nor reducedness appears among the binders.

Dependency interfaces read and used:

- `def-weil-pbc-flat-ring-map`: `Mathlib.RingTheory.RingHom.Flat`, `RingHom.Flat`;
  its full definition uses `f.toAlgebra` and `Module.Flat R S`.
- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; `isNoetherianRing_iff_ideal_fg` verifies the exact meaning.
- `def-weil-pbc-localization-at-prime`: `Mathlib.RingTheory.Localization.AtPrime.Basic`,
  `Localization.AtPrime`, the actual quotient localization at `Q.primeCompl`.
- Primaryness is the existing Mathlib `Ideal.IsPrimary` from
  `Mathlib.RingTheory.Ideal.IsPrimary`, read with `Ideal.isPrimary_iff`.
  The prime index is Mathlib `PrimeSpectrum` from `Mathlib.RingTheory.Spectrum.Prime.Defs`.
- The proof dependency `lem-weil-pbc-flat-tensor-exact` is supplied by
  `Module.Flat.lTensor_exact` and `Module.Flat.rTensor_exact` in
  `Mathlib.RingTheory.Flat.Basic` (plain proof import).
- The proof dependency `lem-weil-pbc-tensor-over-quotient-ring` uses
  `TensorProduct.quotTensorEquivQuotSMul` in
  `Mathlib.LinearAlgebra.TensorProduct.Quotient` and
  `TensorProduct.AlgebraTensorModule.cancelBaseChange` in its public import
  `Mathlib.LinearAlgebra.TensorProduct.Tower`; both signatures/docstrings were read.
- The proof dependency `lem-weil-pbc-module-injects-localizations-associated-primes`
  uses `Module.injective_pi_localization_associatedPrimes` in
  `WeilConjectures.RingTheory.InjectivePiLocalizationAssociatedPrimes`.
  Its full signature includes both injectivity and the elementwise annihilator
  criterion for an arbitrary module, with no finite-generation assumption.
  All proof-only modules are plain imports; statement dependencies are public imports.

Edge cases checked mathematically:

- Empty fibre for a nonfaithfully flat map: take `R = k × k`, let `f : R → k`
  be the first projection and `q = k × 0`. This is a prime (hence primary) ideal,
  `f` is flat as a direct summand, `qS = S`, and no prime above `q` exists.
  The formula is `⊤ = ⊤`.
- The zero target ring is allowed: no `Nontrivial S` is assumed, the spectrum is
  empty, and every ideal is `⊤`, so the equality still makes sense and holds.
  A zero source ring admits no proper primary ideal, consistent with `hq`.
- Nonreduced fibre: take `R = k`, `q = 0`, `S = k[ε]/(ε²)`. The map is flat,
  and localization at the unique prime is the local ring itself. The formula
  recovers zero, without requiring reducedness.
- A nonprime primary ideal is allowed: `R = S = ℤ`, `f = id`, `q = (4)` has
  radical `(2)`; contraction from the localization at `(2)` recovers `(4)`.
- Independent ring universes are retained. Prime indexing is intrinsic to `S`,
  not an arbitrary test-ring universe that could make a hypothesis vacuous.

Searches actually run with `msearch.py N8 lem-per-flat-primary-fibre-recovery`:

- LeanFinder: "A primary ideal extended along a flat ring homomorphism of
  Noetherian rings is the intersection of contractions of its extensions to
  all prime localizations over its radical". Eight hits included
  `Algebra.HasGoingDown.of_flat`,
  `IsLocalization.comap_map_of_isPrimary_disjoint`, faithful-flat lying-over,
  and ideal recovery from principal-open covers. None states the whole-fibre
  recovery of an arbitrary flat extension; that extension need not be primary.
- Loogle: `"Flat", "IsPrimary"`. Zero hits.
- Mathlib grep: `primary.*flat|flat.*primary|comap.*iInf|iInf.*comap` in
  `RingTheory`. Twenty-five hits included lattice map/comap identities,
  principal-open recovery and `comap_localized₀_eq_iInf` from primary
  decomposition uniqueness. The latter's full signature was read: it needs a
  minimal primary decomposition and specifies a different localization formula.
- LeanSearch: "Flat extension of a primary ideal is recovered by localizations
  at all primes contracting to its radical". Eight hits concerned flatness,
  prime localization and structure-sheaf localizations, with no exact match.
- `rg` of `lean/WeilConjectures` and `lean/Sheaf` for
  `primary.*flat|flat.*primary|flat_primary|flatPrimary|fibre_recovery|fibreRecovery`:
  only unrelated primary-component base-change uses were found.
- `grep -rn 'lem-per-flat-primary-fibre-recovery' lean/WeilConjectures`: no hits.
- `rg` of `dag/lean_names_upstream.json`, `lean/WeilConjectures` and `lean/Sheaf`
  for `flatPrimary|flat_primary|map_eq_iInf.*[Pp]rimary|map_eq_iInf_comap`: no hits.

Validation: the prescribed `scompile.py` compiled this file in both sandbox and
library module modes, cleanly (1.5 seconds and 1.4 seconds respectively).
No diagnostic commands, local notation, implicit variables, or additional
axioms are introduced. No statement dispute or source fault was found.

## Second reading by N8

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
