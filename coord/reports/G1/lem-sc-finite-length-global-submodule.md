## Worker report

The module `Sheaf.RingTheory.FiniteLengthGlobalSubmodule` states
`Submodule.length_quotSMulTop_lt_top_of_ringKrullDim_eq_one`, with its sole proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections were needed.
Only the item's `lean` field is changed.

Hypotheses and conclusion, matched individually:

- “R be a domain”: `{R : Type u} [CommRing R] [IsDomain R]`.
- “with fraction field K”: `{K : Type v} [Field K] [Algebra R K]
  [IsFractionRing R K]`; the algebra specifies the canonical R-action and fraction-field
  embedding, and the localization predicate specifies that K is a fraction field of R.
  Independent universes `u v` impose no size restriction between these objects.
- “nonnegative integer r”: `(r : ℕ)`, including zero.
- “M an R-submodule of K^{oplus r}”: `(M : Submodule R (Fin r → K))`.
  The finite coordinate product is the usual finite direct sum: all functions on `Fin r`
  have finite support, with pointwise addition and the R-action induced by `Algebra R K`.
  This retains arbitrary submodules, with no finite-generation assumption on M.
- “R is Noetherian [def-weil-pbc-noetherian-ring]”: `[IsNoetherianRing R]`.
- “of Krull dimension 1 [def-weil-pbc-krull-dimension-ring]”:
  `(hdim : ringKrullDim R = 1)`, equality rather than an upper bound.
- “for every nonzero x in R”: `(x : R) (hx : x ≠ 0)` are universally quantified
  theorem parameters; no nonunit restriction is introduced.
- “the R-module M/xM”: `QuotSMulTop x M`. Here M coerces to its subtype,
  and Mathlib's abbreviation is `M ⧸ x • (⊤ : Submodule R M)`, so the quotient is formed
  inside M, not in the ambient coordinate space.
- “has finite length [def-weil-pbc-module-length]”:
  `Module.length R (QuotSMulTop x M) < ⊤`. `Module.length` takes values in `ℕ∞`;
  strict inequality from top is exactly finite length.

Dependency declarations read in full with their docstrings:

- `def-weil-pbc-noetherian-ring`: Mathlib leaf `IsNoetherianRing` in
  `Mathlib.RingTheory.Noetherian.Defs`; its abbreviation is `IsNoetherian R R`,
  i.e. every ideal is finitely generated.
- `def-weil-pbc-krull-dimension-ring`: Mathlib leaf `ringKrullDim` in
  `Mathlib.RingTheory.KrullDimension.Basic`; the dimension of `PrimeSpectrum R`
  ordered by inclusion, with codomain `WithBot ℕ∞`.
- `def-weil-pbc-module-length`: Mathlib leaf `Module.length` in
  `Mathlib.RingTheory.Length`; the Krull dimension of the submodule lattice,
  with the bottom value removed. Also read `Module.length_ne_top_iff`.
- Supporting existing definitions read: `IsFractionRing` in
  `Mathlib.RingTheory.Localization.FractionRing` and `QuotSMulTop` in
  `Mathlib.RingTheory.QuotSMulTop`. No private copies are used.

Source checked: the local `literature/stacks-project/algebra.tex` is not present on this
machine, so read the official source https://stacks.math.columbia.edu/tag/00PF instead.
The statement there agrees with the node hypothesis by hypothesis. Its current numbering
is Lemma 10.119.11, rather than the node's historical 10.30.9; the stable tag and label
identify the same statement. The theorem docstring carries all four proof steps from the
node and names their dependencies. No statement fault or mathematical dispute found.

Edge cases checked before writing: r = 0 gives the zero coordinate module, hence a zero
submodule and quotient of length zero. M = 0 likewise gives length zero. A nonzero unit x
makes xM = M and the quotient zero; units remain included. M = K^r is also allowed, even
though it need not be finitely generated over R; nonzero x acts invertibly on this M.
For R = ℤ, K = ℚ, r = 1, M = ℤ and x = p prime, the quotient is ℤ/pℤ, of length one.
The zero ring is excluded exactly by “domain”. A field R has dimension zero and fails
only the stated dimension-one hypothesis. No characteristic restriction is present.

Searches actually run (via `/home/ubuntu/weil-launcher/msearch.py`, group G1, this item):

- LeanFinder: `Noetherian domain dimension one arbitrary submodule of finite power of
  fraction field quotient by nonzero scalar has finite length` returned eight hits.
  Closest was `isFiniteLength_quotient_span_singleton`, for R/(x), not arbitrary M/xM.
- Loogle: `IsFiniteLength, Submodule` returned five hits on finite-length modules,
  composition series, and semisimplicity; no matching fraction-field-submodule theorem.
- LeanSearch: `quotient of submodule of fraction field finite length Noetherian dimension
  one` was unavailable (Internal Server Error); this is not a negative match result.
- Mathlib grep: `finite.length|FiniteLength` scoped to `RingTheory/Length` gave zero hits
  (the actual length file is `RingTheory/Length.lean`, not a directory).
- Mathlib grep: `isFiniteLength.*(quot|submodule)|finite.length.global|QuotSMulTop`
  scoped to `RingTheory` returned 25 hits, including the existing quotient abbreviation
  and the R/(x) theorem, but not this statement.
- Local `rg` of the entire source `WeilConjectures` and project `lean/Sheaf` for
  `finite.length|FiniteLength|QuotSMulTop` found quotient uses in regular-sequence and
  projective-dimension files, and unrelated global-dimension prose, not this theorem.
  A node-id search in the entire source `WeilConjectures` returned no hits.
- Local `rg` for `length_quotSMulTop_lt_top_of_ringKrullDim_eq_one` in the source checkout,
  project `lean/Sheaf` and `dag/lean_names_upstream.json` returned no hits.

Validation: server single-file compile and delivery dry run are performed before READY.
The independent second reading is left for the second worker, as required.

## Second reading by G1

Independent reading of the node copy, repository node, delivered module, all three
statement-dependency nodes and their Mathlib declarations. Verdict: the theorem says
exactly what the node says. No Lean or node repair was necessary; this reading and its
search/validation evidence are appended without rewriting the worker report.

Source: read the official Stacks `algebra.tex` at
https://raw.githubusercontent.com/stacks/stacks-project/master/algebra.tex,
including `section-krull-akizuki` and `lemma-finite-length-global` (Tag 00PF), and checked
https://stacks.math.columbia.edu/tag/00PF. The local literature checkout is absent.
The section introduction imposes no standing local-ring or other hypotheses. The lemma
introduces precisely a domain, its fraction field, an arbitrary submodule of a finite
power, Noetherianity, dimension one, and a nonzero scalar. The stable tag agrees despite
renumbering to 10.119.11. No correction or citer review is required.

Objects, hypotheses and conclusion, listed before comparing and checked individually:

1. Commutative domain R: `{R : Type u} [CommRing R] [IsDomain R]`. Exact: Stacks uses
   commutative rings, and a domain is nonzero with no zero divisors.
2. Fraction field K of R: `{K : Type v} [Field K] [Algebra R K]
   [IsFractionRing R K]`. Exact: read `IsFractionRing` in
   `Mathlib.RingTheory.Localization.FractionRing`, where it abbreviates localization
   at `nonZeroDivisors R`. For a domain these are precisely the nonzero elements.
   The algebra provides the specified embedding and its scalar action, not an
   additional field extension or an unrelated module action.
3. Finite nonnegative rank r: `(r : ℕ)`. Exact, with no positivity hypothesis.
4. Arbitrary R-submodule M of K^{oplus r}: `(M : Submodule R (Fin r → K))`.
   Exact: for finite `Fin r`, every function has finite support; the product is the
   finite direct sum with the pointwise R-action. No `Module.Finite R M`, finite
   generation, freeness, or nonzero hypothesis is introduced.
5. R Noetherian: `[IsNoetherianRing R]`. Exact dependency
   `def-weil-pbc-noetherian-ring`: read `Mathlib.RingTheory.Noetherian.Defs`, including
   the abbreviation `IsNoetherian R R` and `isNoetherianRing_iff_ideal_fg`.
6. Krull dimension exactly one: `(hdim : ringKrullDim R = 1)`. Exact dependency
   `def-weil-pbc-krull-dimension-ring`: read `Mathlib.RingTheory.KrullDimension.Basic`
   and `Order.krullDim` in `Mathlib.Order.KrullDimension`. This is the supremum of
   strict prime-ideal chain lengths, with value type `WithBot ℕ∞`. Equality to one
   is neither a dimension bound nor a local dimension assumption.
7. Every nonzero scalar: `(x : R) (hx : x ≠ 0)`. Exact universal theorem parameters
   after R, K, r and M; includes units, and does not quantify x existentially.
8. The quotient R-module M/xM: `QuotSMulTop x M`. Exact: read its declaration in
   `Mathlib.RingTheory.QuotSMulTop`, namely `M ⧸ x • (⊤ : Submodule R M)`.
   Here M coerces to the underlying type of the submodule, so both the scalar-image
   submodule and quotient are inside M, not inside the ambient K^r.
9. Sole conclusion, finite length over R: `Module.length R (QuotSMulTop x M) < ⊤`.
   Exact dependency `def-weil-pbc-module-length`: read `Module.length`,
   `Module.coe_length`, and `Module.length_ne_top_iff` in `Mathlib.RingTheory.Length`.
   Its value in `ℕ∞` is the supremum of strict submodule chain lengths; being below
   top is exactly finite length over R, not cardinal finiteness or length over K.

Edge cases: `r = 0` covers the empty coordinate index; its only submodule is zero.
`M = 0` gives the zero quotient and length zero. For any unit x, xM = M and the
quotient is zero; an empty set of maximal ideals over x therefore poses no missing
case. The full submodule K^r is permitted even when not finitely generated over R.
For R = Z, K = Q, r = 1, M = Z, x a prime, the quotient has length one, illustrating
that finite length differs from zero or vector-space dimension. The zero ring is
excluded by the source's domain hypothesis; a field R is excluded by dimension one.
There is no characteristic assumption. R and K have independent universes u and v,
with no equality or smallness constraint. All variables and universes are explicitly
bound. Empty schemes and other geometric hypotheses do not occur in this node.

Independent searches, using different phrases from the first reader:

- LeanFinder via `msearch.py`: “torsion reduction arbitrary lattice in fraction field
  power one dimensional Noetherian domain finite composition length”. Eight hits:
  Dedekind/PID torsion decompositions, class-number results and an ideal-quotient
  finrank formula. None states this arbitrary-submodule theorem; the decomposition
  signatures require finite generation and stronger ring hypotheses.
- Loogle via `msearch.py`: `Module.length, QuotSMulTop`. Successful query, zero hits.
- LeanSearch via `msearch.py`: “An arbitrary submodule of a finite dimensional fraction
  field vector space modulo a nonzero element has finite module length over a
  Noetherian domain of Krull dimension one”. Internal Server Error, recorded as
  unavailable rather than a negative result.
- `rg` in Mathlib RingTheory, project `lean/Sheaf`, upstream `WeilConjectures` and
  `dag/lean_names_upstream.json`: searched `length.*(fraction|quotSMul|krull)`,
  `finite.*length.*(fraction|dimension)`, `00PF`, `finite-length-global`, and the
  proposed full declaration name. Also read all length-related declarations in
  `RingTheory/Length.lean` and searched the fraction-ring/quotient/length names in
  upstream and project RingTheory. No existing declaration matches.
- Opened the closest Mathlib result
  `isFiniteLength_quotient_span_singleton` in `RingTheory/OrderOfVanishing/Basic.lean`:
  it concludes finite length only for R/(x), not arbitrary M/xM.
  Opened upstream `RingTheory/DiscreteValuationRing/Dominating.lean`, including
  `ValuationSubring.coe_le_ord_of_strictMono`: it bounds chains of ideals of a
  valuation subring; it does not state the requested arbitrary-submodule quotient.
  Thus neither warrants an `existing: true` record.

H4/H12/H13: all notions use existing Mathlib definitions, including the dependency
nodes' recorded declarations. No new definition node, dependency replacement module,
private notion, or missing prerequisite is needed. H5/H6: the module introduces no
definition, axiom, instance or proved theorem; its one theorem has exactly `by sorry`.
H8: both docstrings identify the stable source and blueprint node; the theorem's
four numbered proof steps reproduce the node's unit case, finite set/local theorem,
local detection of strict inclusions, and sum of local length bounds, naming the
relevant dependency nodes. H9: namespace `Submodule`, conventional topic/module,
unique declaration name, permitted imports used by the signature, and lines at most
100 characters. The node's `lean.statement` is verbatim the theorem signature
before `:=`; neither record nor signature needs adjustment.

Validation: `scompile.py G1 lem-sc-finite-length-global-submodule` on the delivered
module exited 0, compiled on the server in 1.3 seconds with no warnings or errors.
Delivery dry run and push follow this independent reading.
