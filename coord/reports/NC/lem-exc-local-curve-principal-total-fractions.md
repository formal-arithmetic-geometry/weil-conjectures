## Worker report

The new module `Sheaf.RingTheory.LocalCurvePrincipalTotalFractions` states
`IsLocalRing.exists_parameter_principal_total_fractions`. Its only theorem has proof
`sorry`; it contains no new definitions or auxiliary postponed assertions. Only `lean`
is changed in the copied item node. There are no statement corrections, new nodes,
dependency repairs, or disputed statements.

Source checked: [Stacks Project, Tag 0C3R, Lemma 33.39.1](https://stacks.math.columbia.edu/tag/0C3R),
the existence assertion and conditions (1), (2), (4), (5), under the reduced-ring
hypothesis. The local literature file is absent, so the source was read online.
The theorem docstring includes all six steps of the DAG proof, with its named
dependencies, including the explicit denominator argument.

Hypothesis and clause correspondence:

- A commutative ring is `(R : Type u) [CommRing R]`, with explicitly declared `universe u`.
- Noetherian is `[IsNoetherianRing R]`: Mathlib's definition is that all ideals are
  finitely generated. No excellence, domain, normalization, or field hypothesis is added.
- Local with its unique maximal ideal is `[IsLocalRing R]`; throughout the conclusion,
  the ideal is `IsLocalRing.maximalIdeal R` (written `maximalIdeal R` in its namespace).
- Reduced is `[IsReduced R]`.
- Dimension exactly one is the named hypothesis `(hdim : ringKrullDim R = 1)`.
  The dimension is Mathlib's chain dimension in `WithBot ℕ∞`, not a domain-specific
  dimension-at-most-one predicate.
- One element satisfying every conclusion is `∃ (f : R) (hf : f ∈ nonZeroDivisors R), ...`.
  The dependent existential binds the proof of regularity so that the canonical
  localization map can use it. This is equivalent to asserting regularity as a
  conjunct; it does not add an assumption on the ring.
- Membership in the maximal ideal is `f ∈ maximalIdeal R`.
- A nonzerodivisor is `hf : f ∈ nonZeroDivisors R`. The commutative-ring lemma
  `mem_nonZeroDivisors_iff_left` identifies this with `∀ x, f * x = 0 → x = 0`,
  exactly the node's definition. Its submonoid contains all powers of `f`.
- Avoiding every minimal prime is `(∀ p ∈ minimalPrimes R, f ∉ p)`.
  These are minimal prime ideals of the zero ideal, as the node requires.
- The ideal `fR` is `Ideal.span ({f} : Set R)`; its radical is Mathlib's `Ideal.radical`.
  The clause is `(Ideal.span ({f} : Set R)).radical = maximalIdeal R`.
  Mathlib's natural-power membership formula permits exponent zero, but that case
  says `1 ∈ I`, so `I = ⊤` and the positive-exponent formulation is equivalent.
- The principal localization is `Localization.Away f`, the recorded dependency's
  construction at `Submonoid.powers f`.
- The total ring of fractions is `FractionRing R`, defined as
  `Localization (nonZeroDivisors R)` without any domain hypothesis. This is the
  `M = R` specialization of the recorded module-localization construction:
  `Localization S` and `LocalizedModule S R` are definitionally equal, as also
  checked in Mathlib's `private lemma example_localization_eq_localizedModule`
  in `Algebra/Module/LocalizedModule/Basic.lean`. No substitute notion is defined.
- The canonical `R`-algebra homomorphism is
  `IsLocalization.Away.liftAlgHom (S := Localization.Away f)
  (f := Algebra.ofId R (FractionRing R)) f
  (IsLocalization.map_units (FractionRing R) ⟨f, hf⟩)`.
  Here `Algebra.ofId` is the structural algebra homomorphism `R →ₐ[R] FractionRing R`;
  `map_units` supplies the unit image of this regular element. The universal lift
  sends `r/f^n` to that same fraction and restricts to the structural map on `R`.
  It is the specified map, with no arbitrary choice of homomorphism or equivalence.
- Being an isomorphism is `Function.Bijective` of that algebra homomorphism.
  A bijective algebra homomorphism has an algebra inverse (`AlgEquiv.ofBijective`),
  and an algebra isomorphism is bijective, so this is exactly the stated property
  of the canonical map, rather than merely existence of an unrelated equivalence.

Recorded statement dependencies used (their full declarations and documentation
were read in the pinned Mathlib source):

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing` (and `isNoetherianRing_iff_ideal_fg`).
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`.
- `def-weil-pbc-module-localization`: `Mathlib.Algebra.Module.LocalizedModule.Basic`,
  `LocalizedModule`, specialized to the ring itself; the ring presentation is
  `FractionRing` in `Mathlib.RingTheory.Localization.FractionRing`.
- `def-weil-ring-localization-away`: `Mathlib.GroupTheory.MonoidLocalization.Away`,
  `Localization.Away`; its algebra lift is supplied by
  `Mathlib.RingTheory.Localization.Away.Basic`, `IsLocalization.Away.liftAlgHom`.

All statement dependency modules are public imports. Further public imports provide
the maximal ideal, minimal-prime set, and the ring structures and canonical map.
The following Mathlib proof-dependency declarations are imported without `public`:
`Ideal.exists_finset_card_eq_height_of_isNoetherianRing` and the local finiteness
instance from `Mathlib.RingTheory.Ideal.KrullsHeightTheorem`;
`IsLocalRing.exists_maximalIdeal_pow_le_of_isArtinianRing_quotient` from
`Mathlib.RingTheory.LocalRing.Quotient`;
`Ideal.iUnion_minimalPrimes` from `Mathlib.RingTheory.Ideal.MinimalPrime.Localization`;
and `PrimeSpectrum.zeroLocus_eq_iff` from `Mathlib.RingTheory.Spectrum.Prime.Topology`.
`IsLocalRing.notMem_maximalIdeal` is already supplied by the public maximal-ideal
import. The height and radical lemmas needed by the proof are also available through
these imports. There are no unpublished Sheaf dependencies or omitted cyclic imports.

Edge cases checked before writing:

- The zero ring has Krull dimension bottom and cannot satisfy dimension one;
  Mathlib's nontrivial local-ring convention therefore discards no intended case.
- Fields have dimension zero and do not meet the hypothesis. No nonfield hypothesis
  is added separately.
- Reducible reduced local curves are retained: no `IsDomain R` instance, no `Field`
  structure on `FractionRing R`, and no nonzero-element replacement for regularity.
  For example, the node of two transverse branches permits a parameter `x + y`
  in the localization of `k[x,y]/(xy)` at `(x,y)`.
- Arbitrary characteristic and arbitrary universe `u` are retained.
- The same `f` appears in maximal-ideal membership, regularity, prime avoidance,
  the radical equality, and the canonical map. A unit cannot satisfy maximal-ideal
  membership, and `0` cannot be a regular parameter in these nontrivial rings.
- Powers include the zeroth power, as required for localization. The proof's
  denominator argument handles a unit denominator with that power.

Searches made on 2026-10-16:

- `msearch.py ... leanfinder` with query
  "A reduced Noetherian local ring of Krull dimension one admits a regular parameter whose principal localization maps isomorphically to the total fraction ring".
  Eight hits include `tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain`,
  `IsDiscreteValuationRing.TFAE`, `IsDedekindDomainDvr`,
  `Ring.KrullDimLE.isField_of_isReduced`, and valuation-ring results. None states
  existence with the four required parameter clauses for a possibly reducible ring.
- `msearch.py ... loogle "IsLocalRing, IsReduced, IsLocalization"`: zero hits.
- `msearch.py ... grep
  "total.*fraction|exists.*nonZeroDivisors.*maximal|exists.*maximal.*nonZeroDivisors"
  RingTheory`: four hits, the `FractionRing` construction, two associated-prime
  facts about Noetherian total fraction rings, and a Picard-group fact; no match.
- `msearch.py ... leansearch` with query
  "A reduced Noetherian local ring of dimension one has a regular parameter whose localization is the total ring of fractions".
  Service unavailable (Internal Server Error); no mathematical verdict inferred.
- `rg -n "principal_total_fractions|total.*[Ff]raction|[Ff]raction.*total|exists.*parameter"`
  over upstream `WeilConjectures` and project `lean/Sheaf` found related project
  results (notably `ReducedNoetherianTotalRingFractions`) but no parameter theorem.
  The upstream tree had no match. The project total-fraction decomposition theorem
  addresses a different assertion and is not a whole-item existing declaration.
- Search for the exact blueprint id in upstream `WeilConjectures` found no match.
  Search for `exists_parameter_principal_total_fractions` in upstream declaration
  names, upstream sources, and project sources found no existing declaration.
- Direct Mathlib source searches located `FractionRing`, `Localization.Away`,
  `IsLocalization.Away.liftAlgHom`, and the nonzerodivisor criterion; these are reused.

Validation: the prescribed `scompile.py NC lem-exc-local-curve-principal-total-fractions`
compiled this module alone, both as a sandbox file and at its library module path,
with no errors or warnings. All variables and the universe are explicitly bound;
the only postponed proof is the item's named theorem. The delivery dry run is
the final worker check; the independent second reader supplies its own section.

## Second reading by NC

I read the item node, its source place (Stacks Project, Tag 0C3R, Lemma 33.39.1), and the module independently. The source says that for a Noetherian one-dimensional local ring, an element in the maximal ideal with radical equal to the maximal ideal is equivalent to avoiding all minimal primes and identifying the principal localization with the product over minimal primes; under depth one (in particular for a reduced ring), these are equivalent to being a nonzerodivisor and identifying the principal localization with the total ring of fractions. The node deliberately specializes this to a reduced ring and requests one common parameter satisfying all listed clauses.

Object and hypothesis correspondence:

- The node's commutative ring (R), with arbitrary universe, is `(R : Type u) [CommRing R]`.
- Noetherian is `[IsNoetherianRing R]`; no excellence, domain, field, or normalization hypothesis is added.
- Locality and the unique maximal ideal are `[IsLocalRing R]` and `IsLocalRing.maximalIdeal R`.
- Reducedness is `[IsReduced R]`.
- Krull dimension exactly one is `(hdim : ringKrullDim R = 1)`.
- The node's existential (f) and its regularity are rendered together as `∃ (f : R) (hf : f ∈ nonZeroDivisors R), ...`; this is a conclusion, not an extra hypothesis.

Conclusion correspondence:

- `f ∈ maximalIdeal R` is membership in the unique maximal ideal.
- `∀ p ∈ minimalPrimes R, f ∉ p` is exactly avoidance of every minimal prime.
- `(Ideal.span ({f} : Set R)).radical = maximalIdeal R` is the stated \\(\\sqrt{fR}=\\mathfrak m\\) clause, using Mathlib's canonical radical.
- The canonical total fraction ring is `FractionRing R`, and the principal localization is `Localization.Away f`.
- The displayed `IsLocalization.Away.liftAlgHom` from `Localization.Away f` to `FractionRing R`, using `Algebra.ofId R (FractionRing R)` and the unit proof for `f`, is the canonical (R)-algebra map. `Function.Bijective` expresses that this map is an isomorphism, with no unrelated equivalence introduced.

No mismatch was found, so no Lean or node correction was needed. The same `f` is used in every conjunct and in the canonical map. The zeroth power is allowed by the localization convention; it handles unit denominators, while the dimension-one and reduced hypotheses exclude the zero-ring and field edge cases intended by the node. Reducible reduced local curves remain covered because no domain or field assumption is imposed. Arbitrary characteristic and universe (u) remain covered.

I searched Mathlib and the project/upstream sources with LeanFinder, Loogle, grep, and the exact declaration/name queries recorded in the worker report. The returned localization, valuation-ring, Krull-dimension, and total-fraction declarations do not state this parameter-existence theorem; no duplicate declaration exists. The Lean file compiles cleanly through the prescribed `scompile.py` check, with only the named theorem proof postponed by `sorry`.
