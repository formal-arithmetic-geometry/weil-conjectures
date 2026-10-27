## Worker report

The delivery states `RingTheory.Rotthaus.finite_boundary_nonzero_contraction` in
`Sheaf.RingTheory.RotthausFiniteBoundary`. Its sole theorem has proof `sorry`.
`Sheaf.RingTheory.RotthausBoundarySystem` supplies concrete semilocal localization,
completion, contracted prime, normalization, canonical map and boundary constructions.
It has no postponed theorem or sorry. The item's statement and proof are unchanged;
only `lean` and the addition of the helper definition to `stmt_deps` change.

Hypothesis and clause correspondence:

- A commutative Noetherian ring: `(B : Type u) [CommRing B] [IsNoetherianRing B]`.
- Nagata: `(hNagata : IsNagataRing B)`, exactly the recorded upstream predicate.
- Element and principal completeness: `(x : B)` and
  `[IsAdicComplete (Ideal.span {x}) B]`. There is no nonzero or nonunit hypothesis.
- G-ring quotient: `(hG : IsGRing (B ⧸ Ideal.span {x}))`.
- Maximal ideal: `(n : MaximalSpectrum B)` includes its maximality certificate.
- `C` is `LocalCompletion x n`, the Mathlib `AdicCompletion` of
  `Localization.AtPrime n.asIdeal` at the image of `x`.
- A prime `s` of `C`: `(s : PrimeSpectrum (LocalCompletion x n))`.
- Singularity: `hs : ¬ IsRegularLocalRing (Localization.AtPrime s.asIdeal)`.
- Minimal singularity: `hmin` quantifies over every prime `t` of `C`, and requires
  regularity of its localization whenever `t.asIdeal < s.asIdeal`.
- The finite sets Γ(n) are exactly `γ : Finset (MaximalSpectrum B)` with `hn : n ∈ γ`.
  The proof `hn` is only an index certificate, not an additional mathematical assumption.
- `denominators γ` is the infimum, over `m : γ`, of the complementary prime submonoids.
  Thus its elements are exactly those outside every maximal ideal of γ, with no
  extra restriction. `Semilocalization γ` is its actual Mathlib localization.
- `Completion x γ` is the principal-adic completion of that localization at the image
  of `x`. `toLocal n γ hn` is the canonical localization algebra homomorphism.
  `completionToLocal` applies the existing `AdicCompletion.principalRingMap`, transported
  along the algebra homomorphism's commutation equality. No arbitrary map is assumed.
- `contractedPrime x n s γ hn` is `PrimeSpectrum.comap` along that map, so its ideal
  is precisely `sγ`. Its prime certificate is supplied by Mathlib's comap.
- `Normalization` is `integralClosure` of the quotient by this contracted prime
  inside the quotient's own `FractionRing`. The quotient is a domain because the
  contracted ideal is prime. Neither a bigger field nor arbitrary normalization data
  is a theorem hypothesis.
- `normalizationMap` is the actual composite from `B` through completion, quotient,
  and the structural inclusion into the integral closure.
- `boundary x n s` is the set of ideals `p` obtained as the contraction of an ideal `Q`
  in some normalization, with `Q ∈ (Ideal.span {normalizationMap ... x}).minimalPrimes`.
  Mathlib minimalPrimes includes primality, containment and minimality. This is literally
  the union of Δγ(x), represented by existential membership rather than a separate Δγ.
- Positive height: `hheight` quantifies over every γ and hn and asks
  `0 < ringKrullDim (Localization.AtPrime (contractedPrime ...).asIdeal)`.
  This is the node's stated local Krull dimension convention, without a height rewrite.
- Finite boundary: `hfinite : (boundary x n s).Finite`.
- Conclusion: `s.asIdeal.comap (algebraMap B (LocalCompletion x n)) ≠ ⊥`, namely
  the contraction to the original ring is not its zero ideal.

Dependencies read and used:

- `Mathlib.RingTheory.AdicCompletion.Basic`: `AdicCompletion`, `IsAdicComplete`,
  with the canonical ring/algebra structures from `.Algebra`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim` (available through the
  regular-local-ring imports).
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`;
  the same localization construction at `denominators γ` supplies the semilocal ring.
- `WeilConjectures.RingTheory.NagataRing`: `IsNagataRing`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `def-weil-regular-scheme`'s retained ring-clause Mathlib match,
  `Mathlib.RingTheory.RegularLocalRing.Defs`: `IsRegularLocalRing`. The node's
  scheme-specific `AlgebraicGeometry.IsRegularScheme` is not needed for this ring lemma.
- `WeilConjectures.RingTheory.GRing`: `IsGRing`.
- The existing node `def-trf-adic-ring-completion-map`, module
  `Sheaf.RingTheory.AdicRingCompletionMap`: `AdicCompletion.principalRingMap`.
  The new helper node cites it; no second completion map construction is introduced.
- For the proof plan, the plain imports expose the stated proof dependencies:
  `IsAdicComplete.le_jacobson_bot`, `Algebra.IsIntegral.of_finite`,
  `Ideal.nonempty_minimalPrimes`, `Ideal.exists_minimalPrimes_le`,
  `RingHom.IsIntegral.comap_surjective`, `AdicCompletion.pow_smul_top_eq_ker_eval`,
  `IsLocalization.isNoetherianRing`, `AdicCompletion.isNoetherianRing`, and
  `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes`.
  The two proof-only nodes `lem-per-bounded-formal-singular-primes-stabilize` and
  `lem-per-bounded-normalization-limit-finite` currently have no Lean record/module,
  so they are named in the proof docstring and cannot yet be imported. They are not
  needed to type this theorem statement and are not restated in this delivery.

Edge cases checked before and after writing:

- `x = 0` remains included. If the contraction is zero, the source proof makes `B`
  a domain; each zero-adic completion is its localization, and positive height is then
  impossible. This is part of Step 1, not a new assumption in Lean.
- A unit `x` is not excluded by a binder; separated completeness at the unit ideal
  would force `B` to be the zero ring, incompatible with the chosen maximal ideal.
- The zero ring is permitted as an ambient type; its lack of maximal ideals makes
  the theorem's data impossible, correctly handling this case without Nontrivial B.
- In a local ring Γ(n) still has its singleton and the construction specializes to
  the local completion. No requirement of multiple maximal ideals occurs.
- Empty γ is allowed for the generic helper (all denominators, the zero localization),
  but is correctly excluded from the theorem's union by `n ∈ γ`.
- The auxiliary quotient is a genuine domain from primality, rather than an additional
  integral-domain assumption on `B`. No injectivity is presupposed.
- `AdicCompletion` includes the zeroth coordinate, whose quotient is the zero ring.
  Omitting that forced coordinate gives the same inverse limit indexed by j ≥ 1.
- `u` is arbitrary; ideals, finite sets, localizations, completions and fraction rings
  stay in the same universe. No test-field or index universe restriction is added.

Searches: `msearch.py` leanfinder queried the full Rotthaus finite-boundary criterion
and returned eight Dedekind valuation, prime-support and related results, none matching.
Loogle query `AdicCompletion.map, Localization.map, integralClosure` had no hits
(`Localization.map` unknown); targeted grep `Rotthaus|Hilfssatz|semilocalCompletion`
had no Mathlib hits. The further helper searches (LeanSearch, LeanFinder, Loogle, grep)
are reproduced verbatim in the new node's `mathlib_searches`.
Direct `rg` in Mathlib, `lean/WeilConjectures`, `lean/Sheaf` and
`dag/lean_names_upstream.json` found no Rotthaus theorem or semilocal-completion boundary
system. Direct source search did find the already recorded principal completion map;
its full module was read and reused. `rg`/the requested blueprint-id search found no
upstream declaration for this item. `blueprint_refs.py search 'semilocal completion'`
returned zero blueprint matches; the targeted DAG scan located only the relevant
statement nodes, not a definition node for the boundary system. The example
`CompactObject.lean` is currently a withdrawn empty module; its node record and the
current module-system conventions were read instead of reproducing its retired code.

Source check: the published PDF of Kurano–Shimomoto was opened at Theorem 5.3,
printed p.11: its Γ(n), localization map, contracted prime, normalization, Δ(x),
positive-height hypothesis and conclusion match the constructions here. The accepted
node additionally retains the G-ring quotient assumption from its reviewed
Nishimura–Nishimura proof route. No new dispute or correction was introduced; the
stage-1 review already recorded why the two completion arguments supply that premise.
There is no released repair note for this item.

Validation: both delivered modules compile cleanly through `scompile.py`, separately
in dependency order against the published live library (all passes below three seconds).
The helper has real data throughout; the main theorem's proof is exactly `sorry`.

## New nodes

`def-per-rotthaus-boundary-system` packages the literal constructions in
Kurano–Shimomoto Theorem 5.3: denominators, semilocal fractions, principal completions,
the canonical map to the selected local completion, contraction, normalized quotient,
its map from the original ring and the union of contracted principal minimal primes.
It adds no property or theorem. Its own module uses the existing Mathlib objects
and the already landed `AdicCompletion.principalRingMap`. The theorem now cites this
new definition node. Searches in the DAG, Mathlib and both project roots found no
existing node or public definition carrying this system. The new node's search
records contain the exact service output, including Loogle's unknown-name response.

## Second reading by Q82

A separate pass reread the node beside the final theorem and expanded every helper
as listed above. This is the dispatcher's single-worker self-check; no second agent
was started, as explicitly instructed. The maintainer's independent review is still
required. I checked particularly that the map to C is canonical, that normalization
uses the quotient's own fraction field, and that the boundary involves minimal primes
in Eγ and contracts all the way to B. I also checked that `hheight` uses local dimension,
that minimal singularity quantifies over all strictly smaller primes, and that `x = 0`
has not been removed. No mathematical mismatch was found. Compiler repairs made the
prime-comap import explicit and transported the canonical principal completion map
along `AlgHom.commutes`; they did not change any mathematical assumption or conclusion.
No statement correction or dependency-module repair was necessary.
