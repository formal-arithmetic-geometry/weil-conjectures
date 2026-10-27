## Worker report

The module `Sheaf.RingTheory.AdicQuotientIsomorphismsLocalize` states
`Localization.adic_quotient_isomorphisms_localize`, with its entire proof `sorry`.
There are no new definitions, auxiliary postponed theorems, dependency repairs, or
statement corrections. The node changes only in `lean`.

Source read: `literature/stacks-project/algebra.tex`, Tag 00CT,
`proposition-localize-quotient`, lines 1380–1425, including both explicit inverse
fraction maps. The node extracts the prime-extension, ideal-power, and transition
calculations from an application of that proposition. Its six proof steps are
included in the theorem docstring.

Hypothesis and conclusion correspondence:

- Commutative rings C and D: `{C : Type u} {D : Type v} [CommRing C] [CommRing D]`.
  The independent explicit universes impose no size equality.
- The unital ring homomorphism is `(f : C →+* D)`.
- Prime ideals are `(p : Ideal C) (Q : Ideal D) [p.IsPrime] [Q.IsPrime]`.
- Contraction is `(hpQ : p = Q.comap f)`, the symmetric form of the node's equality.
- Extension of an ideal K is Mathlib's `K.map f`, defined as the span of `f '' K`.
- For every integer n at least one, the canonical global quotient map is an
  isomorphism: `hquot : ∀ n : ℕ, 1 ≤ n → Function.Bijective
  (Ideal.quotientMap ((p ^ n).map f) f Ideal.le_comap_map)`.
  This is the actual map sending `[c]` to `[f c]`, rather than an arbitrary
  isomorphism of the two rings. Bijectivity of this ring homomorphism is precisely
  the ring-isomorphism assertion.
- `Q = pD` is the first conjunct `Q = p.map f`.
- Equality of powers for all positive exponents is
  `∀ n : ℕ+, Q ^ (n : ℕ) = (p ^ (n : ℕ)).map f`.
- The canonical local map is the existing
  `Localization.localRingHom p Q f hpQ`. Its definition and
  `Localization.localRingHom_mk'` give exactly `c/s ↦ f(c)/f(s)`.
- Its inverse-image assertion is the third conjunct: the comap of
  `Q.map (algebraMap D (Localization.AtPrime Q))` is
  `p.map (algebraMap C (Localization.AtPrime p))`.
- The family `e : ∀ n : ℕ+, ... ≃+* ...` gives ring isomorphisms between
  the quotients by the powers of precisely these extended primes. Mathlib
  identifies these primes with the maximal ideals of the localizations.
- The first property of `e` explicitly sends
  `Ideal.Quotient.mk _ (IsLocalization.mk' (Localization.AtPrime p) c s)` to
  `Ideal.Quotient.mk _ (IsLocalization.mk' (Localization.AtPrime Q) (f c) ...)`.
  The target denominator is `f s`, with membership in `Q.primeCompl` supplied by
  `le_comap_primeCompl_iff.mpr (ge_of_eq hpQ) s.2`. Every source element has
  a fraction representative; this property characterizes the isomorphism as the
  map induced by the canonical local homomorphism, without any arbitrary choice.
- For every positive `k n` with `hnk : n ≤ k` and every element `x` of the
  exponent-k source quotient, the last conjunct says
  `e n (Ideal.Quotient.factor (Ideal.pow_le_pow_right hnk) x) =
  Ideal.Quotient.factor (Ideal.pow_le_pow_right hnk) (e k x)`.
  These are the canonical quotient transition maps on each side. Equality on
  every element is equivalent to equality of the composite ring homomorphisms.

Dependencies and APIs read and used:

- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
  Its full definition is localization at `p.primeCompl`. The same module supplies
  `Localization.localRingHom`, `localRingHom_mk'`, and its local-hom instance.
  No replacement localization or local map is defined.
- Proof dependency `lemma-nagata-localization-ideal-pow`:
  `Mathlib.RingTheory.Ideal.Maps`, `Ideal.map_pow`, used in proof Step 2.
  This module is already publicly imported by the statement's Mathlib imports.
- Proof dependency `lem-weil-pbc-localization-at-prime-of-quotient` has no
  `lean` record and is a Mathlib leaf. Read its `mathlib_match`: the quotient
  localization instance in `Mathlib.RingTheory.Localization.Ideal`,
  `Ideal.map_primeCompl_comap_of_surjective` in `Mathlib.RingTheory.Ideal.Maps`,
  and `IsLocalization.algEquiv` / `algEquiv_mk'` in
  `Mathlib.RingTheory.Localization.Basic`. The first module is imported privately
  for proof Step 4; Maps and Basic are already imported transitively.
- The statement also uses `Ideal.quotientMap` and `Ideal.Quotient.factor` from
  the standard quotient API, `Ideal.pow_le_pow_right` for transitions, and `ℕ+`
  to index every positive integer. No canonical-map helper is missing.

Edge cases checked before writing:

- Exponent one is included in both the hypothesis and local family; it is
  precisely what establishes `Q = pD`.
- `k = n` is allowed, giving the identity reductions, without a strict inequality.
- A nonmaximal prime is allowed: for the identity on `k[x,y]` at `(x)`, the
  local residue field is `k(y)`. No maximality or finite residue field was assumed.
- The zero prime of a domain is allowed; local quotients then give the
  corresponding fraction-field comparison. No nonzero-prime assumption occurs.
- Nilpotents are allowed: the identity on `ℤ/4ℤ` at `(2)` satisfies the assertion,
  including exponents where the prime power becomes zero. No reducedness,
  domain, Noetherian, separation, flatness, or injectivity hypothesis was added.
- Trivial rings admit no prime ideals, so the explicit prime hypotheses naturally
  exclude that nonexistent case. Rings themselves are not required nontrivial.
- Index zero is outside the node's positive-exponent claims; `ℕ+` removes exactly
  that index, and `hquot` uses `1 ≤ n` explicitly.

Searches performed (all via the prescribed wrapper or read-only rg):

1. LeanFinder through `msearch.py`: "A ring map inducing isomorphisms modulo all
   powers of a prime gives compatible isomorphisms on quotients of localizations
   at primes lying over it." Eight hits, including `Localization.localRingHom`,
   `quotMapEquivQuotMapMaximalIdealOfIsLocalization`, and AtPrime extension and
   Dedekind-prime correspondence lemmas. None asserts the full result; the local
   map is reused. The maximal-ideal quotient comparison has a maximality
   hypothesis absent here.
2. Loogle through `msearch.py`: `Ideal.quotientMap, Function.Bijective`.
   Successful search, zero hits.
3. Mathlib grep through `msearch.py`, restricted to `RingTheory/Localization`:
   `localRingHom|quotientMap.*bijective|bijective.*quotientMap`.
   Five hits, all the localRingHom definition and its scalar/fraction formulas.
4. LeanSearch through `msearch.py`: "A ring homomorphism inducing isomorphisms
   modulo every positive power of a prime induces compatible isomorphisms of
   the corresponding local prime-power quotients." Eight hits including
   `Ideal.Quotient.factorPow`, `factorPowSucc`, `Localization.isLocalHom_localRingHom`,
   and unrelated p-adic reduction maps. No exact theorem found. The statement
   uses the more general existing `Ideal.Quotient.factor` on the power inclusion.
5. Read-only rg on `lean/WeilConjectures`, `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for
   `adic.*quotient.*localiz|quotient.*isomorphisms.*localiz|adic_quotient_isomorphisms_localize`.
   Hits concern a local G-ring criterion, derived localization, and the completed
   tensor-base-change consumer `AdicBaseTensorLocalComparison`; none states this
   general ring-map theorem. The latter module was opened and checked: it uses
   the present node in its proof, with substantially stronger completion and
   finiteness hypotheses in its own statement.
6. Read-only rg on `lean/WeilConjectures` for the exact item ID: no hits.
   Additional rg on both source roots for `localRingHom` and local quotient names
   found consumers of the existing Mathlib map, not an exact statement.

Validation: prescribed `scompile.py` compiled both its sandbox module and the
library-named module cleanly (5.9 s and 4.2 s), with no errors or unexpected warnings.
The final explicit auto-implicit options are also checked in delivery preflight.
No statement dispute or source fault was found.

## Second reading by Q132

Final in-thread rereading compared the node, the complete signature, and Tag 00CT.
The conjunction order matches prime extension, powers, local contraction, then the
isomorphism family with its fraction formula and all transition squares. The
`hpQ` orientation is deliberately reversed for Mathlib's `localRingHom`; it has
the identical content. Positive natural indices cover exactly the stated
integers, and the source and target extended primes have not been interchanged.
`hquot` refers to the induced quotient map, and the denominator in the formula is
specifically `f s`, rather than an arbitrary unit. No mismatch required changing
the node. Explicit auto-implicit settings were added for the final check.
This is the worker's final rereading; the maintainer supplies the independent
review under the dispatcher brief, which forbids starting other agents.
