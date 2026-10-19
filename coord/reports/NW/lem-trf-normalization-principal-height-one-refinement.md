## Worker report

The module `Sheaf.RingTheory.NormalizationPrincipalHeightOneRefinement` states
`Ideal.exists_heightOne_prime_le_of_mem_integralClosure`, with one deferred proof
(`by sorry`) and no new definitions. The node is unchanged outside `lean`. No new
node, dependency repair, statement correction, or disputed statement is needed.

Source read: Swanson–Huneke, *Integral Closure of Ideals, Rings, and Modules*,
Theorem 4.10.5 proof, printed p. 91 (PDF page 105, zero-based page 104), paragraph
introducing the principal-height refinement; author-hosted PDF at
https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf. The node isolates
that subclaim for local R and does not assume the later Krull-domain conclusion.
The supplied six-step DAG argument is retained in the theorem docstring: pass
through R[b], preserve the integral closure by transitivity, obtain the finite
local model, apply the Noetherian principal-height bound downstairs, lift a prime
by lying over and bound its chains using incomparability, then contract through
the localization correspondence. This avoids assuming N Noetherian.

Hypotheses and clauses, matched individually:

| Node | Lean rendering |
| --- | --- |
| R is a commutative ring | `(R : Type u) [CommRing R]` |
| R is a nonzero ring without zero divisors | `[IsDomain R]` |
| R is Noetherian | `[IsNoetherianRing R]` |
| R is local | `[IsLocalRing R]`, the standard equivalent local-ring predicate |
| K is the fraction field of R | `(K : Type v) [Field K] [Algebra R K] [IsFractionRing R K]` |
| N is its integral closure inside K | The canonical Mathlib subalgebra `integralClosure R K` is used everywhere |
| b belongs to N | `(b : integralClosure R K)` |
| b is nonzero | `(_hb : b ≠ 0)` |
| P is an ideal of N and is prime | `(P : Ideal (integralClosure R K)) [P.IsPrime]` |
| P contains b | `(_hbP : b ∈ P)` |
| There exists an ideal Q of N | `∃ Q : Ideal (integralClosure R K), ...` |
| Q is prime | `Q.IsPrime` |
| Q is contained in P, equality permitted | `Q ≤ P` |
| Q contains b | `b ∈ Q` |
| Q is nonzero | `Q ≠ ⊥` |
| No prime lies strictly between zero and Q | `∀ q : Ideal (integralClosure R K), q.IsPrime → q < Q → q = ⊥` |
| No Noetherianity hypothesis on N | There is no such instance or hypothesis |

The last clause is precisely the node's definition of height one: since zero
is least among ideals, every prime strictly below Q must be zero. This directly
states the node's characterization without introducing a second definition of
height one or assuming a Dedekind-domain structure. It also agrees with the
inline height-one condition used by the downstream normalization/Krull module.

Statement dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` and `isNoetherianRing_iff_ideal_fg`. The definition says all
  ideals are finitely generated, exactly the node; the signature and docstring
  were read at lines 194–211 of the pinned source.
- `def-weil-pbc-integral-closure`:
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`, `integralClosure`, whose
  carrier is `{x | IsIntegral R x}`. Read its full construction at lines 215–228
  and the polynomial-root definition of `IsIntegral` in `IsIntegral.Defs`.

Additional standard interfaces read: `IsFractionRing` is localization at
`nonZeroDivisors R`, with `[Field K]` giving the fraction-field presentation;
`IsLocalRing` in `LocalRing.Defs` is the nontrivial-ring unit-sum predicate,
equivalent for commutative rings to having a unique maximal ideal. The arbitrary
universes `u v` and every binder are explicit, and `autoImplicit` is disabled.

Proof dependency imports (all are ordinary, non-public imports):

| Dependency | Module and declaration read |
| --- | --- |
| finite local model | `Sheaf.TraceFormula.NormalizationFiniteLocalModel`, `exists_finiteType_intermediate_algebra_isolating_prime` |
| finite type implies Noetherian | `Mathlib.RingTheory.FiniteType`, `Algebra.FiniteType.isNoetherianRing` |
| finite integral generators | `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (public statement import, reexporting `IsIntegral.Basic`), `Algebra.finite_adjoin_of_finite_of_isIntegral` |
| finite implies integral | `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (public statement import), `Algebra.IsIntegral.of_finite` |
| integrality transitive | `Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic`, `RingHom.IsIntegral.trans` |
| minimal prime contained in a prime | `Mathlib.RingTheory.Ideal.KrullsHeightTheorem` (importing `MinimalPrime.Basic`), `Ideal.exists_minimalPrimes_le` |
| height quotient bound | `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`, `Ideal.height_le_height_add_encard_of_subset` |
| integral lying over | `Mathlib.RingTheory.Spectrum.Prime.Topology`, `RingHom.IsIntegral.comap_surjective` |
| incomparability | `Mathlib.RingTheory.Ideal.GoingUp`, `Ideal.IsIntegral.comap_lt_comap` |
| localization prime correspondence | `Sheaf.RingTheory.LocalizationPrimeResidueFieldIso`, `IsLocalization.prime_localRing_residueField_iso`, clause (1) |

No import of the downstream `NormalizationIntegralClosureKrull` module is needed;
its height-one indexing subtype is not a new prerequisite of this subclaim.
Every recorded statement dependency has a usable Mathlib declaration. All proof
dependencies' stated modules are accessible through the listed imports.

Edge cases checked before writing:

- If R is a field, N is a field and a nonzero b lies in no prime. The theorem is
  vacuous through `_hbP`, and does not assert that a field has height-one primes.
- More generally a unit b cannot satisfy `_hbP`; no nonunit hypothesis is added.
- b = 0 is excluded exactly by `_hb`; otherwise P = zero would falsify the claim.
- P = zero is impossible with `_hb` and `_hbP`. The zero ring is excluded by the
  node's domain hypothesis, rather than by an extra assumption.
- Q = P is permitted and is necessary when P itself has height one.
- No finite-dimensionality, finite-generation of N, excellence, characteristic,
  or Noetherianity of N is assumed. Infinite height of P is permitted.
- The universes of the base and fraction field are independent; all ideal and
  element variables belong to the actual integral closure in that fraction field.

Searches actually run with `msearch.py` (also logged in `searches.jsonl`):

1. LeanFinder: “Every prime containing a nonzero element in the integral closure
   of a Noetherian local domain in its fraction field contains a height one prime
   containing that element”. Eight hits concerning Dedekind domains, primes over
   ideals and finite integral extensions; none gives this statement.
2. LeanFinder: “Every prime containing a nonzero element in the normalization of
   a Noetherian domain contains a height one prime containing that element”. Eight
   hits, principally `IsDedekindDomain.HeightOneSpectrum` and normalized-factor
   lemmas. These require unavailable hypotheses, and none is an exact match.
3. Loogle: `"integralClosure", "height"`. Zero hits.
4. Mathlib grep: `height_le_one_of_isPrincipal_of_mem_minimalPrimes|exists_minimalPrimes_le`
   under `RingTheory`. Twenty-two hits, including minimal-prime existence and
   Krull's principal ideal theorem. Read the relevant signatures: the height
   theorem assumes the ambient ring is Noetherian. Applying it directly to N
   would add a forbidden assumption.
5. LeanSearch: “For a Noetherian local domain every prime of its normalization
   containing a nonzero element contains a height one prime containing that
   element”. Eight hits: Noetherian height bounds, Dedekind height-one spectra,
   and a going-down height formula; no exact theorem for this normalization.
6. Direct `rg` in the pinned `WeilConjectures` sources, shared `lean/Sheaf`, and
   `dag/lean_names_upstream.json` for this node id and height/refinement names.
   Upstream has no occurrence of the node id. The project has the downstream
   `NormalizationIntegralClosureKrull` docstring citing the item, but no theorem
   stating it. The new declaration's full name is absent from all these sources
   and from Mathlib. The project's finite-local-model and principal-radical
   modules were read; neither states the requested refinement.

Validation: `scompile.py NW lem-trf-normalization-principal-height-one-refinement`
compiled the finite-local-model overlay, the sandbox statement, and the library
module separately within the 60-second limit. All completed without errors or
warnings; the theorem has exactly the intended deferred proof. Delivery dry run
and final delivery use the prescribed wrapper and the server preflight.

## Second reading by NW

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
