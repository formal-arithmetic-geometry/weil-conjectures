## Worker report

The module `Sheaf.RingTheory.MaximalChainLengthOfDepth` states
`IsLocalRing.maximal_chain_length_eq_of_depth` with a `sorry` proof. No definition is
introduced. The original node is unchanged except for its `lean` record.

Hypothesis and clause correspondence:

- The Noetherian local commutative ring `(S, m)` is `{S : Type u} [CommRing S]
  [IsNoetherianRing S] [IsLocalRing S]`. Mathlib's local-ring predicate includes
  nontriviality, exactly as “exactly one maximal ideal” does. Its maximal ideal is
  `IsLocalRing.maximalIdeal S`, used by the recorded depth definition.
- Finite dimension `d = dim S` is `(d : ℕ)` and
  `hdim : ringKrullDim S = (d : WithBot ℕ∞)`. This specifies a finite dimension
  without adding a separate finiteness hypothesis.
- Cohen–Macaulay in the stated depth sense is
  `hdepth : (d : ℕ∞) ≤ IsLocalRing.depth (R := S) S`. The explanatory regular-sequence
  clause is already the definition of depth through `RingTheory.Sequence.IsRegular`
  on `S` as an `S`-module, with entries in its maximal ideal. It is not a separate
  assumption or a private Cohen–Macaulay predicate. In this Noetherian local finite
  dimensional setting, the supremum condition means there is such a sequence of
  length at least `d`, whose initial `d` entries are regular, hence one of length `d`.
- A chain `p₀ ⊊ ... ⊊ pₙ` is `(n : ℕ)` and
  `p : Fin (n + 1) → PrimeSpectrum S`, with `hp : StrictMono p`.
  `PrimeSpectrum` bundles exactly an ideal and its primality proof. Its partial order
  is lifted from inclusion of ideals. Thus there are `n + 1` primes and `n` inclusions.
- The maximality condition is
  `hmax : IsMaxChain (fun q r : PrimeSpectrum S ↦ q ≤ r) (Set.range p)`.
  Mathlib defines this as a chain admitting no strictly larger chain. For a finite
  strictly ordered chain, any extra comparable prime must occur before the first,
  between consecutive primes, or after the last. Conversely, any such insertion
  produces a larger chain. This is precisely the node's maximality condition.
  The parenthetical minimal first prime, maximal last prime, and saturated gaps are
  consequences of this condition in a local ring, not additional hypotheses.
- The conclusion `n = d` is rendered verbatim as `n = d`.

Dependency declarations read and used:

- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`, the abbreviation for
  Noetherianity of the self-module; its ideal finite-generation characterization
  is `isNoetherianRing_iff_ideal_fg`.
- `Mathlib.RingTheory.KrullDimension.Basic`: `ringKrullDim`, the dimension of
  `PrimeSpectrum S` ordered by inclusion, with values in `WithBot ℕ∞`.
- `Sheaf.RingTheory.Depth`: `IsLocalRing.depth` and `Ideal.depth`.
  The former uses the maximal ideal and the latter takes the supremum of lengths
  of regular sequences in that ideal, except the `IM = M` case gives infinity.
- `Mathlib.RingTheory.Regular.RegularSequence`: `RingTheory.Sequence.IsRegular`
  is used through the depth module. Its `IsWeaklyRegular` parent expresses
  injective multiplication modulo the preceding entries; `top_ne_smul` expresses
  the nonzero final quotient. No redundant direct import is added.
- For the chain, Mathlib's `PrimeSpectrum` and `IsMaxChain` were read in full,
  including the inclusion-induced partial order and the no-larger-chain definition.

Edge cases checked before writing: `d = 0` and `n = 0` are allowed. A singleton
prime chain is maximal exactly when it is both minimal and maximal; the theorem
then gives dimension zero. A field supplies this case with depth zero. The zero
ring is excluded by the node's local-ring requirement, as by Mathlib's
`IsLocalRing` nontriviality. No empty chain is introduced: the node itself has
`p₀`, and `Fin (n + 1)` is always nonempty. Arbitrary ring universes are allowed
by explicitly bound `universe u`; every other binder is explicit. Infinite and
bottom dimensions are excluded by the given finite natural dimension equality.

Source read: [Stacks Tag 00N9](https://stacks.math.columbia.edu/tag/00N9) and its
ring-specialized proof in [Tag 0AAE](https://stacks.math.columbia.edu/tag/0AAE).
The local literature checkout is absent, so the primary-source pages were opened.
The declaration docstring reproduces all eight proof steps from the DAG and names
all proof dependencies needed at each non-elementary step. No statement fault,
correction, or disputed statement was found.

Searches for an existing statement (2026-10-11):

- `msearch.py ... leansearch "Every maximal chain of prime ideals in a Cohen
  Macaulay local ring has length its dimension"`: UNAVAILABLE, Internal Server
  Error; no verdict inferred from the failed service.
- `msearch.py ... leanfinder "Every maximal chain of prime ideals in a Cohen
  Macaulay Noetherian local ring has length equal to its Krull dimension"`: eight
  hits, including `ringKrullDim_quotient_span_singleton_succ_eq_ringKrullDim`,
  `Ideal.primeHeight_eq_ringKrullDim_iff`, and
  `IsLocalRing.maximalIdeal_primeHeight_eq_ringKrullDim`; none states this result.
- `msearch.py ... loogle "ringKrullDim, LTSeries"`: zero hits.
- `msearch.py ... grep "CohenMacaulay|Cohen.Macaulay|maximal.chain" RingTheory`:
  zero hits in Mathlib ring theory.
- `rg -n "CohenMacaulay|Cohen.Macaulay|maximal.chain|IsMaxChain"` in the source
  `WeilConjectures` and project `lean/Sheaf`: only a topological dimension comment
  in the upstream source; no corresponding theorem. The requested node-id search
  in `WeilConjectures` also returned no match.
- `rg` in Mathlib's `Order/Preorder/Chain.lean` found the usable existing
  `IsMaxChain`; reading its definition confirms the exact maximality condition.
- Name-collision search for `maximal_chain_length_eq_of_depth|length_eq_of_depth`
  in `dag/lean_names_upstream.json`, Mathlib, source, and project: no matches.

Validation: server single-file compilation passed cleanly (exit 0, 1.4 seconds).
The first delivery dry run required the recorded signature to stop before `:=`;
that metadata was repaired without changing the theorem. The independent second
reading is left to the second reader; the delivery dry run is repeated below.

## Second reading by K1

Independent reading of the repository node, sandbox node and Lean module, all four
statement dependency nodes, and the dependency declarations themselves. Verdict:
the Lean states exactly the node. No mathematical, signature, or docstring repair
was needed; this second-reading report is the only change.

Objects, hypotheses, and conclusion checked separately:

- Commutative ring S: `{S : Type u} [CommRing S]`, with explicitly bound
  `universe u`. Verdict: the same ring, unrestricted universe and characteristic.
- Noetherian: `[IsNoetherianRing S]`. Read the recorded abbreviation in
  `Mathlib.RingTheory.Noetherian.Defs` and `isNoetherianRing_iff_ideal_fg`:
  precisely every ideal finitely generated. Verdict: exact.
- Local ring with maximal ideal m: `[IsLocalRing S]`. Read its nontriviality
  superclass and the landed `IsLocalRing.depth` definition, which uses
  `IsLocalRing.maximalIdeal S`. Verdict: the unique maximal ideal is implicit,
  with no extra instance assumption beyond the node's local ring.
- Finite natural dimension d: `(d n : ℕ)` and
  `hdim : ringKrullDim S = (d : WithBot ℕ∞)`. Read the recorded
  `ringKrullDim` definition and `Order.krullDim`: the supremum of strict prime
  chain lengths, not a topological dimension with reversed chain conventions.
  Verdict: exact finite dimension, no stronger dimension restriction.
- Cohen–Macaulay depth condition: `hdepth : (d : ℕ∞) ≤
  IsLocalRing.depth (R := S) S`. Read both definitions in the dependency module
  `Sheaf.RingTheory.Depth`: self-module, maximal ideal, supremum of lengths of
  regular sequences contained in that ideal. The needed `Module.Finite S S`
  instance is automatic for the ring over itself, not an added hypothesis.
  Since the maximal ideal is proper, its product with S is not S, so the
  exceptional infinity branch does not intervene. For positive finite d the
  supremum bound ensures a sequence of length at least d; its initial d entries
  are regular. For d = 0 the empty sequence is regular on nonzero S. Verdict:
  exactly depth at least d, including the explanatory sequence clause.
- Regular sequences: opened the dependency's recorded Mathlib declaration
  `RingTheory.Sequence.IsRegular`, its `IsWeaklyRegular` parent, and
  `top_ne_smul`. They express injective multiplication on each preceding
  quotient and nonzero final quotient. Verdict: the dependency notion is exact
  and used through depth; no private copy or missing dependency module.
- Prime ideals p0 through pn: `p : Fin (n + 1) → PrimeSpectrum S`.
  Read `PrimeSpectrum` in its Defs module: ideal plus primality, with order
  lifted by `asIdeal`. Verdict: precisely n + 1 prime ideals.
- Strict inclusions: `hp : StrictMono p`. The spectrum order is ideal inclusion
  (`asIdeal_lt_asIdeal` is definitionally equivalent). Verdict: exactly the
  node's n strict inclusions, including nonadjacent comparisons by transitivity.
- Maximal chain: `hmax : IsMaxChain (fun q r : PrimeSpectrum S ↦ q ≤ r)
  (Set.range p)`. Read `IsChain` and `IsMaxChain` in
  `Mathlib.Order.Preorder.Chain`. Any extra member of a larger chain is
  comparable with all finitely many entries, hence can be inserted before,
  between, or after them; any such insertion yields a larger chain. Verdict:
  exactly insertion maximality, not maximum possible length. The minimal first
  prime, terminal maximal ideal, and saturated gaps are its consequences.
- Conclusion: `n = d`. Verdict: exact, with both natural numbers universally
  quantified before the hypotheses and the universally quantified chain.

Source: the local Stacks checkout is absent. Read the actual primary-source
`algebra.tex` from
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
labels `definition-local-ring-CM`, `lemma-maximal-chain-CM`, and
`lemma-maximal-chain-maximal-CM`, and the contextual section
https://stacks.math.columbia.edu/tag/00N7 plus Tags 00N9 and 0AAE. The source
assumes a commutative Noetherian local ring, not a field or an algebra of finite
type. The source's general module theorem specializes to M = S, whose support
is the whole spectrum; no support hypothesis is missing in the ring case.
The eight docstring proof steps match all eight node steps, including replacing
x by a positive power, the associated-prime argument ensuring the quotient
chain starts at a minimal prime, and the induction over all such local rings.

Edge cases: d = 0 and n = 0 are admitted, including fields. A singleton maximal
chain is both minimal and maximal, as required. An empty chain is not in the
node and is not introduced by `Fin (n + 1)`. The zero ring is excluded by exactly
one maximal ideal in the node and by `IsLocalRing` nontriviality in Lean.
Infinite and bottom dimension do not meet the stated finite dimension premise.
There is no scheme, independent index set, field, characteristic condition, or
second module universe to restrict. Every variable and universe is bound.

Independent searches (2026-10-11), using words different from the first reader:

- LeanSearch via msearch: "In a Noetherian local ring depth equal to Krull
  dimension forces every saturated maximal prime chain to have the same length".
  Service unavailable (Internal Server Error), recorded without a no-match verdict.
- LeanFinder via msearch: "A saturated prime ideal chain from a minimal prime to
  the maximal ideal in a local ring with depth equal to dimension has dimension
  many strict steps". Eight hits: `Ideal.exists_ltSeries_length_eq_height`,
  height/dimension comparison theorems, and `ringKrullDim`; none asserts every
  maximal chain has the dimension's length. The existential height chain result
  has a different quantifier and does not replace this item.
- Loogle via msearch: `IsMaxChain, PrimeSpectrum`: zero hits.
- Mathlib grep via msearch in RingTheory:
  `catenar|equidimension|saturated.*chain|chain.*depth`: zero hits.
- Direct rg of upstream `WeilConjectures`, project `lean/Sheaf`, and
  `dag/lean_names_upstream.json`, with the preceding pattern and the proposed
  declaration name: only the project Dimension module's equidimensional-fibre
  comment. Opened it: it is about relative scheme dimension, not this theorem.
  No statement or declaration-name collision was found.

There are no new definition nodes, dependency modules, or statement_change in
this delivery. Existing dependency definitions are sufficient and non-hollow.
The sole theorem proof remains `sorry`, with all eight proof steps and source
references documented; nothing was proved. Imports and namespace follow the
contract, every Lean line is within 100 characters, and the node's recorded
signature matches the file verbatim up to (excluding) `:=`.

Second-reader validation: scompile passed on the server (exit 0, 1.4 seconds,
no warnings). deliver2 --no-push printed OK: preflight and compile passed,
nothing pushed. The initial compile invocation used a repository-relative path;
repeating it with the absolute sandbox module path resolved that path error.
