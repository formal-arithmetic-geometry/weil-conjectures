## Worker report

The module `Sheaf.RingTheory.ParameterProductPrimeFamilyMatching` states
`IsLocalRing.parameterProductPrimeFamilyMatching`, with its whole proof postponed by `sorry`.
It introduces no definitions. The node is unchanged except for `lean`.
No statement fault or STATEMENT-DISPUTED issue was found.

Hypotheses and objects, matched against the node:

- `A : Type u`, `R : Type v`, `[CommRing A]`, `[CommRing R]`, and `φ : A →+* R`
  give the arbitrary homomorphism of commutative rings. Neither locality, injectivity,
  flatness nor an algebra structure is imposed on the homomorphism.
- `[IsRegularLocalRing R]` is the regular-local-ring clause, including Noetherianity
  and locality. The dependency `def-weil-regular-scheme` records this ring predicate in
  its unchanged `mathlib_match`. The separate scheme declaration
  `AlgebraicGeometry.IsRegularScheme` was read; this ring-only statement needs no scheme.
- `{d r : ℕ}`, `t : Fin d → R`, and
  `ht : IsRegularSystemOfParameters (List.ofFn t)` specify the ordered full parameter list.
  The recorded definition says its span is the maximal ideal and its length, cast into
  `WithBot ℕ∞`, equals `ringKrullDim R`. Since `List.ofFn t` has length `d`, this also
  says the dimension is `d`; no independent dimension premise is necessary.
- `hr : r ≤ d` gives the chosen initial sublist; the natural-number binder includes `0 ≤ r`.
  Its factors are `t (Fin.castLE hr i)` for `i : Fin r`, the zero-based version of indices
  `1,...,r`. Their product is `∏ i : Fin r, t (Fin.castLE hr i)`, equal to one for `r = 0`.
  The expression is written directly throughout, with no hidden let or auxiliary notion.
- `I : Ideal A` and `F : Type w` with `[Finite F]` give an ideal and an arbitrary finite
  indexing set. All three universes are explicit and independent; emptiness is allowed.
- `p : F → Ideal A`, `hp : ∀ a, p a ∈ I.minimalPrimes`, and
  `hp_distinct : Function.Injective p` give exactly the distinct primes minimal over `I`.
  `Ideal.minimalPrimes` includes primality, containment of `I`, and absence of a strictly
  smaller prime containing `I`. No completeness assumption on this selected family is added.
- `q : F → Ideal R` and `hq : ∀ a, (q a).IsPrime` give the proper primes upstairs.
  Mathlib's `Ideal.IsPrime` includes properness, so it needs no additional inequality.
- `hcontraction : ∀ a, Ideal.comap φ (q a) = p a` gives exactly the specified contractions.
- `hV` is the equality of `PrimeSpectrum.zeroLocus` of the principal product ideal with
  `⋃ a : F, PrimeSpectrum.zeroLocus (q a : Set R)`. The arguments are the underlying sets
  of the ideals; the definition of zero locus is precisely the set of prime ideals containing
  that underlying set, hence the node's `V(J)`.

Conclusions, in their order in the conjunction:

- `∀ i : Fin r, (Ideal.span {t (Fin.castLE hr i)}).IsPrime` asserts each parameter ideal
  is a proper prime.
- `Pairwise fun i j : Fin r ↦ ¬ Ideal.span {t (Fin.castLE hr i)} ≤
  Ideal.span {t (Fin.castLE hr j)}` says distinct indices give incomparable ideals.
  Pairwise quantifies over both ordered pairs, so neither containment is allowed.
- Equality of the product ideal's `minimalPrimes` with the `Set.range` of those principal
  ideals says these are exactly all minimal primes over the product.
- `∃! e : F ≃ Fin r, ∀ a, q a = Ideal.span {t (Fin.castLE hr (e a))}` states the existence
  and uniqueness of the required bijection, together with every specified ideal equality.
  Equivalences include both injectivity and surjectivity, and the uniqueness quantifies
  over equivalences satisfying the equality, not merely over their range.
- `r = 0 → IsEmpty F` is the final assertion that the family must be empty.

Dependency declarations read and used:

- `WeilConjectures.RingTheory.IsRegularSystemOfParameters`, declaration
  `IsLocalRing.IsRegularSystemOfParameters`, public imported directly. Its full definition
  is the maximal-ideal span equality and the list-length Krull-dimension equality.
- `Mathlib.RingTheory.RegularLocalRing.Defs`, declaration `IsRegularLocalRing`, as recorded
  by `def-weil-regular-scheme.mathlib_match`, publicly available through the parameter module.
  Its full class extends `IsLocalRing` and `IsNoetherianRing`, with maximal-ideal spanFinrank
  equal to ring Krull dimension. Its sibling `IsRegularRing` and the recorded scheme module
  were also inspected, but are not needed by this local ring statement.
- `Mathlib.RingTheory.Ideal.MinimalPrime.Basic`, declarations `Ideal.IsMinimalPrime` and
  `Ideal.minimalPrimes`; the former is `Minimal (fun q ↦ q.IsPrime ∧ I ≤ q) p`.
- `Mathlib.RingTheory.Spectrum.Prime.Basic`, declaration `PrimeSpectrum.zeroLocus`, read with
  its full docstring and definition `{x | s ⊆ x.asIdeal}`.

The sole proof dependency `lem-sfb-transverse-prime-ideal-parameters` has no Lean record or
Mathlib match in the read repository, so there is no stated proof module to import. Its
clause (b) is cited in the proof docstring as the reviewed source of the parameter-prime,
incomparability and minimal-prime assertions. The remaining four proof steps are written
out there, including the two-sided containment, contraction minimality, injectivity,
surjectivity, and uniqueness. No proof-dependency declaration was copied or invented.

Sources inspected: `literature/stacks-project/more-algebra.tex`, label
`lemma-regular-local-UFD` (Tag 0AG0), especially its opening proof that a parameter is prime.
The current blueprint ancestor `literature/blueprint/latest/blueprint/sec-trace-formula/
sk-i-curve-zero/lem-trf-local-term-locality.md` was read; as the accepted split records,
this is an extracted algebra argument, not a literal assertion of that ancestor's text.
The parent module `Sheaf.TraceFormula.EtaleComponentCoordinateIdentification` was also read.

Edge cases checked before writing:

- In dimension zero the parameter list is empty and `hr` forces `r = 0`. No positivity or
  nonempty index premise excludes this case.
- For `r = 0`, the product is one, its ideal is the whole ring, its zero locus is empty,
  its minimal-prime set and the parameter-ideal range are both empty. If a label existed,
  its proper prime would belong to its own zero locus, contradicting `hV`. The empty
  equivalence with `Fin 0` is the unique matching.
- For `r > 0` an empty family cannot satisfy `hV`: a parameter prime contains the product
  and gives a point of its nonempty zero locus.
- In `k[x,y]_(x,y)` with the full parameter product `xy`, the primes `(x)` and `(y)` are
  incomparable and are matched as expected, with identity contraction as an example.
  Adding the redundant prime `(x,y)` violates the minimal-contraction hypothesis.
- Repeated labels with the same contraction violate `hp_distinct`, as required. The map
  `φ` may have a kernel; the proof uses only monotonicity of contraction, not injectivity.
- The zero ring is excluded exactly by regular-local-ring locality, not by an extra premise.

Searches for an existing exact statement (2026-10-24):

- `msearch.py ... leanfinder` query: "A finite family of primes with distinct contractions
  minimal over an ideal is uniquely matched with regular parameter principal primes when
  their vanishing sets have the same union". Eight hits included
  `Ideal.IsMinimalPrimaryDecomposition`, its `distinct` lemma,
  `Ideal.exists_comap_eq_of_mem_minimalPrimes`, and
  `Ideal.exists_minimalPrimes_comap_eq`. These concern decompositions or prime lifting,
  not the specified parameter-family matching; no exact statement.
- `msearch.py ... loogle` query: `"minimalPrimes", "prod"`. Zero hits.
- `msearch.py ... grep` query:
  `minimalPrimes.*(prod|span)|span.*minimalPrimes|IsRegularSystemOfParameters`, under
  `RingTheory`. Seven hits in spectrum chains, ideal UFD and Krull height material;
  no prime-family matching declaration.
- `msearch.py ... leansearch` query: "A finite family of prime ideals with distinct minimal
  contractions is bijective with principal parameter primes when their zero loci cover
  the zero locus of the parameter product". Eight hits, including `PrimeSpectrum.zeroLocus`,
  `minimalPrimes`, sigma/product spectrum bijectivity, and prime-over declarations.
  These supply standard notions or different bijections, not this statement.
- `rg` over `lean/WeilConjectures` and `lean/Sheaf` for
  `prime.*[Ff]amily.*[Mm]atching|parameterProduct|parameter_product|parameter.*[Mm]atching|
  IsRegularSystemOfParameters` found the existing parameter definition and consumers,
  including the geometric parent statement; no exact algebraic statement. An exact-node-id
  `grep -rn` in `lean/WeilConjectures` had no hits. A focused `rg` for the proposed declaration
  and parameter/matching variants in both Lean roots and `dag/lean_names_upstream.json`
  had no hits. The parent gives étale geometric coordinates, not this arbitrary ring-map
  prime matching. No existing declaration is restated.

Validation: the required `scompile.py Q56 lem-trf-parameter-product-prime-family-matching`
compiled the module against the published live library, both as a sandbox file (6.4 s)
and at its library module path (2.9 s), without errors or unexpected warnings.
All source lines are at most 100 characters; `autoImplicit` is explicitly disabled.
The signature in `lean.statement` is copied verbatim from the theorem keyword to its proof.

## Second reading by Q56

A separate self-review pass reopened the node and final module and checked the full signature
against the statement, rather than relying on the compilation. No other agent was started,
as the dispatcher's brief forbids that; the maintainer supplies the independent review.
This pass checked the distinctions between a selected family and all minimal primes,
between primeness and maximality, between incomparability and mere distinctness, and between
a bijection's existence and uniqueness. It verified the implicit dimension condition in `ht`
via `List.ofFn` length, the arbitrary ring-map universes, properness within `IsPrime`, the
ideal-valued minimal-prime range, and the empty equivalence clause. No mathematical mismatch
was found. The only change was lowercasing a sentence continuation in the proof docstring.
No definitions, dependency repairs, new nodes, or statement corrections are included.
