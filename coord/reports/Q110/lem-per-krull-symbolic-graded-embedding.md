## Worker report

The module `Sheaf.RingTheory.KrullSymbolicGradedEmbedding` states
`Ideal.exists_injective_symbolicPow_quot_succ`, with a single `sorry` proof.
No definitions, auxiliary theorems, new nodes, dependency repairs, or statement
corrections are needed. The node copy changes only `lean`.

Source read: Swanson–Huneke, *Integral Closure of Ideals, Rings, and Modules*,
Definition 4.10.1 and Theorem 4.10.7, printed pp.89 and 92–93, online PDF
https://www.math.purdue.edu/~iswanso/book/SwansonHuneke.pdf, PDF pages 102 and
105–106 (zero-based). Definition 4.10.1 gives precisely the three Krull conditions.
The first two proof paragraphs of 4.10.7 give the intermediate symbolic-power
embedding, before using Noetherianity of the prime quotient. The item's complete
six-step denominator-clearing proof is reproduced in the declaration docstring.
The latest blueprint ancestor `lem-per-artin-gabber-affine-curve.md` and its proof
were read; this is an auxiliary algebra input in its recorded DAG chain, not the
unit statement itself.

Hypotheses and clauses, matched individually:

- Commutative integral domain: `(D : Type u) [CommRing D] [IsDomain D]`.
- Fraction field: `(F : Type v) [Field F] [Algebra D F] [IsFractionRing D F]`.
  The independent universes allow every fraction-field presentation of `D`.
- A height-one prime is represented by `Q : PrimeSpectrum D` together with
  `Q.asIdeal ≠ ⊥` and
  `∀ q : PrimeSpectrum D, q.asIdeal < Q.asIdeal → q.asIdeal = ⊥`.
  Since zero is prime in a domain, this is exactly the given chain definition;
  no finite-dimensional or Noetherian condition is implicit here.
- Condition (i) is `hlocal`, quantified over exactly these primes. Its three
  conjuncts are `IsNoetherianRing`, `IsDomain`, and `IsIntegrallyClosed` on
  `Localization.AtPrime Q.asIdeal`. The last two mean normal domain, as prescribed
  by the normal-ring dependency record.
- Condition (ii) is `hinter`. `Set.range (algebraMap D F)` is the copy of `D` in
  `F`. `Localization.subalgebra F Q.asIdeal.primeCompl
  Q.asIdeal.primeCompl_le_nonZeroDivisors` is the canonical copy of `D_Q` in `F`,
  not an arbitrary map or an existentially chosen localization. The indexed set
  intersection includes all and only height-one primes. An empty intersection
  is `Set.univ`, i.e. the whole fraction field.
- Condition (iii) is `hfinite`: for each `a ≠ 0`, the set of height-one points
  whose ideals contain `a` is `Set.Finite`. `PrimeSpectrum` has precisely one
  point per prime ideal, so this is the stated finiteness condition on ideals.
- The fixed height-one prime is `(P : Ideal D) [P.IsPrime]` with `hP`, using the
  same nonzero and minimal-nonzero-prime conditions as the other primes.
- The degree `(n : ℕ)` covers every integer `n ≥ 0`, including zero.
- Each written symbolic power is literally
  `Ideal.comap (algebraMap D (Localization.AtPrime P))
    ((P.map (algebraMap D (Localization.AtPrime P))) ^ n)`.
  `Ideal.map` is extension, the power is the ordinary ideal power in `D_P`, and
  `Ideal.comap` is inverse image along `a ↦ a/1`. Thus the definition is exactly
  `{a ∈ D | a/1 ∈ (PD_P)^n}`. No separate symbolic-power definition is introduced.
- The numerator is this ideal viewed as its natural `D`-submodule. The denominator
  is `Submodule.comap` of the next symbolic power along the numerator's
  `.subtype`. Since ideal powers decrease, its carrier is exactly the next
  symbolic power as a submodule of the numerator. This avoids needing a
  well-definedness proof merely to write the quotient. It is the actual quotient
  `P^(n)/P^(n+1)`, not the quotient of the ambient ring.
- The conclusion `∃ f : (...) →ₗ[D] (D ⧸ P), Function.Injective f` gives exactly
  an injective `D`-linear map to `D/P`. All actions and quotient structures are
  Mathlib's canonical ones. Neither the existence of a canonical map nor a
  surjectivity assertion is added.
- There is no assumption `IsNoetherianRing D` or `IsNoetherianRing (D ⧸ P)`.

Dependency declarations read and used:

- `def-weil-pbc-localization-at-prime`:
  `Mathlib.RingTheory.Localization.AtPrime.Basic`, `Localization.AtPrime`.
  Its signature and docstring specify localization at the prime complement.
- `def-weil-pbc-noetherian-ring`:
  `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`; the adjacent
  `isNoetherianRing_iff_ideal_fg` confirms the ideal-finiteness interpretation.
- `def-weil-pbc-normal-ring`:
  `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`, `IsIntegrallyClosed`
  together with `IsDomain`, exactly the dependency's recorded domain form.
- The canonical ambient-field construction is the existing
  `Localization.subalgebra` from `Mathlib.RingTheory.Localization.AsSubring`;
  its full signature, real construction, and docstring were read.
- The quotient and restricted denominator use Mathlib's `Submodule.comap`,
  `Submodule.subtype`, and quotient-module structure, not custom copies.
- All recorded proof dependencies that have declarations are imported:
  `IsLocalization.AtPrime.orderIsoOfPrime` (public localization import),
  `IsLocalization.orderIsoOfPrime` (the same import's localization-ideal dependency),
  the recorded regular-local criterion in
  `WeilConjectures.AlgebraicGeometry.Regular` (plain proof import), and
  `IsDiscreteValuationRing` with
  `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible` in
  `Mathlib.RingTheory.DiscreteValuationRing.Basic` (plain proof import).
  No proof-only imports are promoted to public statement dependencies.

Edge cases checked mathematically before writing:

- `n = 0`: ideal power zero is top, its comap is all of `D`, and contraction
  of `PD_P` is `P`. The conclusion is the identity embedding of `D/P`.
- Empty height-one spectrum: `hinter` means `D = F`. The fixed `P` cannot then
  satisfy `hP`; no spurious height-one-prime case is asserted or excluded.
- A field satisfies the three Krull conditions with empty height-one spectrum
  and supplies no `P`; the zero ring is correctly excluded by `IsDomain`.
- For `D = k[x,y]`, `P = (x)`, the quotient is the expected rank-one piece.
- For `D = k[x,y,z]/(xy-z²)`, `P = (x,z)`, ordinary powers and symbolic powers
  differ: `x ∈ P^(2)`. The actual comap-of-localized-power expression retains
  this element, so the signature has not silently substituted ordinary powers.
- Infinite collections of height-one primes are allowed. Only the primes
  containing a particular nonzero element are assumed finite.

Searches actually run for this item:

- `msearch.py` LeanFinder, query “consecutive symbolic powers at a height one
  prime of a Krull domain embed into its prime quotient”: eight hits, including
  `Ideal.pow_succ_lt_pow` and ramification quotient maps. These require a
  Dedekind domain or describe different modules and do not state this result.
- `msearch.py` Loogle, query `Ideal.symbolicPower, Ideal.powQuotSuccInclusion`:
  no hits; unknown identifier `Ideal.symbolicPower`.
- `msearch.py` grep, query `symbolic|KrullDomain`, subdirectory `RingTheory`:
  two comment hits in polynomial Eisenstein criteria; no symbolic-power or
  Krull-domain definition or embedding theorem.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for symbolic powers and
  `KrullDomain`: only proof prose in `LocalGenericUnitFactorization` and
  unrelated “symbolic” comments. The item's id has no upstream Lean hit.
- `rg` in Mathlib, the upstream and project Lean trees, and
  `dag/lean_names_upstream.json` for `exists_injective_symbolicPow_quot_succ`:
  no declaration clash.
- Read `Ideal.quotEquivPowQuotPowSucc` in
  `Mathlib/RingTheory/Ideal/IsPrincipalPowQuotient.lean`: it concerns ordinary
  powers of a principal ideal of the original domain and is not a match here.
- Read `ReflexiveHeightOneIntersection.lean`: its height-one intersection
  criterion concerns finite reflexive modules over a Noetherian normal domain,
  not this non-Noetherian Krull-domain assertion.

Validation: `scompile.py Q110 lem-per-krull-symbolic-graded-embedding` compiled
both the sandbox and named-library forms cleanly, in 1.5 and 1.6 seconds.
Every variable and universe is explicitly bound. The file has no diagnostic
commands or local notation, and its sole theorem proof is `sorry`.
No statement dispute or source-based correction is needed.

## Second reading by Q110

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
