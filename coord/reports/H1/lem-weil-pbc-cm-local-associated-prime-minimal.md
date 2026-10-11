## Worker report

The module `Sheaf.RingTheory.AssociatedPrimeMinimalOfDepth` states
`Ideal.mem_minimalPrimes_of_depth_ge`, with a single `sorry` proof and no definitions.
The statement is unchanged from the DAG. No new nodes or dependency modules are needed.

Hypothesis and conclusion correspondence:

- The commutative ring T is `{T : Type u} [CommRing T]`, with the universe explicitly bound.
- Noetherian is `[IsNoetherianRing T]`.
- Local with unique maximal ideal n is `[IsLocalRing T]`. Its maximal ideal is the one used
  by `IsLocalRing.depth T`; there is no separately chosen ideal requiring an equality binder.
- Finite Krull dimension e = dim T is `(e : ℕ)` and
  `(hdim : ringKrullDim T = (e : WithBot ℕ∞))`. This names the finite dimension, without
  imposing a new restriction: a Noetherian local ring has finite nonnegative dimension.
- Cohen–Macaulay in the node's explicit sense depth(T) >= e is
  `(hdepth : (e : ℕ∞) ≤ IsLocalRing.depth (R := T) T)`. The node's following phrase about a regular
  sequence of length e explains this condition; it is not another independent hypothesis.
  The recorded depth definition uses precisely regular sequences in the maximal ideal.
- The prime ideal is `(p : Ideal T) (hp : p.IsPrime)`.
- Existence of z with Ann_T(z) = p is
  `(hassoc : ∃ z : T, ∀ a : T, a ∈ p ↔ a * z = 0)`.
  This is equality of the two subsets by extensionality, written elementwise exactly as
  the node spells out its annihilator. No nonzero hypothesis on z is added: primality
  already excludes z = 0, whose annihilator would be the unit ideal.
- The conclusion that p is minimal among prime ideals is `p ∈ minimalPrimes T`.
  Mathlib defines this as minimality among primes containing the zero ideal, equivalently
  `Minimal Ideal.IsPrime p`; hence no prime ideal is strictly contained in p.

Dependencies read and used:

- `def-weil-pbc-noetherian-ring`: `Mathlib.RingTheory.Noetherian.Defs`,
  `IsNoetherianRing`; read its docstring, signature, and `isNoetherianRing_iff_ideal_fg`.
- `def-weil-pbc-krull-dimension-ring`: `Mathlib.RingTheory.KrullDimension.Basic`,
  `ringKrullDim`; the definition is the order dimension of the prime spectrum.
- `def-weil-pbc-depth`: `Sheaf.RingTheory.Depth`, `IsLocalRing.depth`, referring to
  `Ideal.depth`; read the full definitions and docstrings. The former specializes the
  latter to `IsLocalRing.maximalIdeal T`, and `T` is the finite module over itself.
- `def-weil-pbc-regular-sequence`: its mathlib_match is
  `Mathlib.RingTheory.Regular.RegularSequence`, `RingTheory.Sequence.IsRegular`.
  Read its full signature, parent `IsWeaklyRegular`, and docstrings; this notion is used
  through the recorded depth definition and imported transitively by Depth.

Also read Mathlib's `IsLocalRing` and `minimalPrimes` definitions. No private copies are
introduced. The proof docstring includes both DAG steps: the associated-prime depth
bound, then the contradiction obtained by prepending a smaller prime to a lifted chain.

Sources read: the local literature checkout lacks `literature/stacks-project/algebra.tex`,
so read the authoritative Stacks pages directly:
[Tag 0BUS](https://stacks.math.columbia.edu/tag/0BUS) and
[Tag 00N8](https://stacks.math.columbia.edu/tag/00N8).
The former gives the associated-prime minimality assertion for Cohen–Macaulay modules;
the latter specializes the notion to the ring as its own module.

Edge cases checked: e = 0 is included and the empty regular sequence is allowed by the
recorded depth definition. Fields are included, with zero ideal minimal and depth zero.
The zero ring is excluded by the local-ring hypothesis itself (Mathlib's IsLocalRing
extends Nontrivial), matching the node's requirement of exactly one maximal ideal.
z = 0 cannot satisfy the prime-annihilator hypothesis. Nilpotents and zero divisors
are allowed, and there is no domain, reducedness, characteristic, or algebra-over-field
restriction. Infinite Krull dimension does not occur for a Noetherian local ring; the
natural dimension binder does not discard a case of the node. No statement fault or
dispute was found.

Searches for an existing statement (msearch.py, group H1, this item):

- leanfinder: `Associated primes of a Cohen Macaulay Noetherian local ring are minimal primes`.
  Eight hits: results about dimension-zero minimal primes, fraction-ring associated
  primes, primary ideals and height zero. None states the Cohen–Macaulay assertion.
- loogle: `ringKrullDim, associatedPrimes, IsLocalRing.depth`: zero hits.
- leansearch: `Associated primes of Cohen Macaulay local rings are minimal primes`:
  unavailable, Internal Server Error; no conclusion inferred from this unavailable service.
- grep: `CohenMacaulay|associatedPrimes.*depth|depth.*associatedPrimes|associated.*minimal`
  in Mathlib/RingTheory: zero hits.
- Local rg: `CohenMacaulay|associated.*minimal|depth.*associated|cm_local_associated|` followed
  by this item's exact id in WeilConjectures and lean/Sheaf: only unrelated comments or
  hypotheses about minimal associated primes in HilbertAffineDenominatorModule,
  RemoveEmbeddedPrimes and TotalQuotientRingMinimalProduct; no declaration matching.
  The exact node id has no source match.
- Local rg: `cm_local|minimalPrimes.*depth|mem_minimalPrimes_of_depth` in
  dag/lean_names_upstream.json, lean/Sheaf and WeilConjectures: zero hits.

Validation: server single-file compilation and deliver2.py --no-push are run before
handing this sandbox to the second reader. No second-reading section is authored here.


## Second reading by H1

Independent second reader opened the item node, the delivered Lean module, all four
statement dependency nodes and their recorded declaration sources. The following is my
object/hypothesis/conclusion checklist, in the order of the node.

- Object: a commutative ring T, with no size restriction. Rendered by `{T : Type u}`,
  `[CommRing T]` and the explicitly declared `universe u`. Verdict: exact.
- Hypothesis: T is Noetherian. Rendered by `[IsNoetherianRing T]`.
  Read Mathlib Noetherian/Defs: `IsNoetherianRing` is `IsNoetherian T T`, and
  `isNoetherianRing_iff_ideal_fg` identifies this with finite generation of every ideal.
  Verdict: the recorded dependency, exact, with no extra assumption.
- Object and hypothesis: the unique maximal ideal n of the local ring T.
  Rendered by `[IsLocalRing T]`; `IsLocalRing.depth` uses `maximalIdeal T`.
  Read LocalRing/Defs and the complete Sheaf.RingTheory.Depth module. Locality is
  nontriviality plus the usual units criterion, equivalent for commutative rings to
  having exactly one maximal ideal. There is no need to choose n separately.
  Verdict: exact; no choice of a different ideal is hidden in depth.
- Object and hypothesis: finite Krull dimension e = dim T. Rendered by `(e : ℕ)`
  and `hdim : ringKrullDim T = (e : WithBot ℕ∞)`. Read KrullDimension/Basic:
  `ringKrullDim T` is the order Krull dimension of `PrimeSpectrum T`. The casts
  preserve finite chain lengths. Noetherian local rings have finite dimension,
  so the natural-number binder does not add a restriction. Verdict: exact.
- Hypothesis: depth(T) >= e, equivalently a T-regular sequence of length e in n.
  Rendered by `hdepth : (e : ℕ∞) ≤ IsLocalRing.depth (R := T) T`.
  The recorded depth specializes `Ideal.depth` to the maximal ideal and takes the
  supremum of lengths of `RingTheory.Sequence.IsRegular T` lists therein. Read the
  regular-sequence dependency and Mathlib Regular/RegularSequence, including
  `IsWeaklyRegular.regular_mod_prev` and `IsRegular.top_ne_smul`: successive
  multiplication is injective and the final quotient is nonzero. For T itself the
  maximal ideal times T is proper, so depth's infinity-by-fiat branch is irrelevant.
  Taking T as its own finite module is automatic, with generator 1, rather than an
  added finiteness premise. Verdict: exact. The regular-sequence phrase explains the
  same depth hypothesis, not a second condition that must be bound independently.
- Object and hypothesis: p is a prime ideal. Rendered by `(p : Ideal T)` and
  `(hp : p.IsPrime)`. Verdict: exact; primality includes properness.
- Hypothesis: there exists z in T whose annihilator is p. Rendered by
  `hassoc : ∃ z : T, ∀ a : T, a ∈ p ↔ a * z = 0`.
  Equality is expressed by equality of membership, with exactly the node's order of
  existential and universal quantifiers. This is an annihilator, not its radical.
  Verdict: exact; no nonzero or nonzerodivisor assumption added.
- Conclusion: no prime ideal is strictly contained in p. Rendered by
  `p ∈ minimalPrimes T`. Read MinimalPrime/Basic: this is minimality among primes
  over the zero ideal, and `minimalPrimes_eq_minimals` identifies it with
  `Minimal Ideal.IsPrime p`. Verdict: exact; it is not minimality merely among
  associated primes or primes over the annihilator of the chosen element.

Source check: the local literature checkout has no stacks-project directory. I read
both Stacks web pages https://stacks.math.columbia.edu/tag/0BUS and
https://stacks.math.columbia.edu/tag/00N8, and independently read the authoritative
raw algebra.tex at https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
including `section-CM`, `definition-CM`, `lemma-CM-ass-minimal-support` and
`definition-local-ring-CM` with surrounding text. The lemma assumes a Noetherian
local ring and a finite Cohen-Macaulay module; for M = T its support is the whole
spectrum and its finite generation is automatic. Definition-CM says depth equals
support dimension; the node uses the equivalent lower bound, using the standard
upper bound named in its source record. There are no further standing base-field,
characteristic or reducedness assumptions. The module docstring follows both node
proof steps: the associated-prime depth bound, and lifting a quotient chain then
prepending a strictly smaller prime to contradict dim T = e.

Edge cases: e = 0 and the empty regular sequence are included; fields are included.
The zero ring is excluded already by exactly-one-maximal-ideal locality, as in the
node, and by Mathlib IsLocalRing's Nontrivial parent. z = 0 cannot meet hassoc and hp,
since its annihilator is the unit ideal. Arbitrary characteristic, nilpotents and zero
divisors are allowed. Universe u is unrestricted; there is no field or algebra
instance. Empty schemes and external index sets do not occur in this statement.

Independent searches, using different wording from the first worker:

- msearch.py leanfinder: `In a local Cohen Macaulay ring a prime annihilator of a ring
  element has height zero`: eight hits, on Krull's principal ideal theorem, heights,
  regular quotients and localization at minimal primes; none is this statement.
- msearch.py loogle: `"associatedPrimes", "depth"`: zero hits.
- msearch.py leansearch: `A prime ideal which is the annihilator of an element of a
  Cohen Macaulay local ring is minimal`: unavailable (Internal Server Error).
  No mathematical absence verdict is inferred from that service failure.
- rg over pinned Mathlib/RingTheory, WeilConjectures, repository lean/Sheaf and
  dag/lean_names_upstream.json for `cohen.?macaulay|unmixed|embedded.*prime|` followed
  by `annihilator.*minimal|depth.*minimalPrimes|minimalPrimes.*depth|` followed by
  `mem_minimalPrimes_of_depth_ge`: no equivalent theorem. I opened the closest
  project hit, `Ideal.annihilator_eq_iff_mem_minimalPrimes_of_fg`: it compares
  association with weak association over an element's annihilator, not minimality
  over zero, and is not a substitute for this item. Other hits concern removing
  embedded primes or assume their absence.

No mismatch found; no Lean or node change needed. There are no new definition nodes,
no dependency modules, no private definitions and no statement correction to review.
The only theorem proof is sorry; every binder and universe is explicit. Imports
supply the actual depth, Noetherian and Krull-dimension notions used. Checked the
100-character convention and exact verbatim equality of lean.statement to the
signature extracted from the delivered file.
