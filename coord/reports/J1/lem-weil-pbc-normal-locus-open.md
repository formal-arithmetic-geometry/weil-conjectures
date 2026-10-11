## Worker report

The module `lean/Sheaf/Paper/NormalLocusOpen.lean` states
`AlgebraicGeometry.normal_locus_isOpen`. It binds a commutative ring `R`, the
Noetherian and domain hypotheses, a nonzero element `f`, and the hypothesis that
`Localization.Away f` is a domain and integrally closed. Its conclusion is that
the set of prime spectrum points whose `Localization.AtPrime` is a domain and
integrally closed is `IsOpen`.

The Noetherian hypothesis is `[IsNoetherianRing R]`; integrality and normality
are rendered by `IsDomain` and `IsIntegrallyClosed` as required by the normal-ring
convention. The principal localization is `Localization.Away f`, and localization
at a prime is `Localization.AtPrime p.asIdeal`. The affine spectrum topology is
Mathlib's `PrimeSpectrum` and `IsOpen`.

Dependency notions were checked in the node records. `def-weil-pbc-noetherian-ring`
uses Mathlib `IsNoetherianRing`; the other dependency records have no Lean
record, while the corresponding notions are supplied directly by Mathlib
(`Localization.Away`, `Localization.AtPrime`, `IsIntegrallyClosed`, and
`PrimeSpectrum`).

Edge cases checked: `f ≠ 0` is explicit; the empty normal locus is allowed by
`IsOpen`; prime localizations are indexed by all `PrimeSpectrum R` points.

Searches: `msearch.py leanfinder` and `loogle` for normal locus openness found no
matching theorem; grep of Mathlib found only local integral-closedness lemmas and
no normal-locus declaration; grep of `WeilConjectures/` and `lean/Sheaf/` found no
existing declaration of this statement.

## Earlier second reading (a previous round; superseded)

The theorem signature was reread against the node clause by clause. `R` is a
commutative Noetherian integral domain, `f` is nonzero, and `Localization.Away f`
is normal in the stated domain plus integral-closed sense. The conclusion uses
exactly the set of primes with normal prime localization and asserts openness.
No mismatch was found.

## Second reading by J1

I opened the sandbox node and Lean module, each of the five statement dependency
nodes, their recorded declarations/mathlib matches in the pinned Mathlib source,
and Stacks algebra.tex on the server (the literature checkout is absent locally).
The source's lemma-openness-normal-locus, Tag 0332, explicitly assumes a
Noetherian domain and a nonzero f with R_f normal. The surrounding algebra
conventions are commutative rings; no finite-type, field, excellence, dimension,
or characteristic hypothesis is assumed. There is no statement_change and no
new definition node or dependency module in this delivery.

Clause-by-clause list and verdicts (H3):

- Object R, a commutative ring: `{R : Type u} [CommRing R]`. Exact; u is declared
  explicitly and arbitrary.
- Hypothesis R Noetherian: `[IsNoetherianRing R]`. Exact.
  `def-weil-pbc-noetherian-ring` records Mathlib.RingTheory.Noetherian.Defs;
  its `IsNoetherianRing` is `IsNoetherian R R`, and
  `isNoetherianRing_iff_ideal_fg` states precisely finite generation of every ideal.
- Hypothesis R integral domain: `[IsDomain R]`. Exact, including nontriviality.
- Object f and hypothesis existence of a nonzero such element: `(f : R)` and
  `(hf : f ≠ 0)`. Exact witness-taking form: an existential witness can be
  eliminated into these binders, and the conclusion does not depend on the witness.
- Object R_f: `Localization.Away f`. Exact: the declaration in
  Mathlib.GroupTheory.MonoidLocalization.Away is `Localization (Submonoid.powers f)`,
  with its ring/algebra structures from RingTheory.Localization.Away.Basic.
  This is precisely the usable mathlib_match of def-weil-ring-localization-away;
  no replacement dependency module is needed despite its absent lean record.
- Hypothesis R_f normal domain: `hf_normal : IsDomain (Localization.Away f) ∧
  IsIntegrallyClosed (Localization.Away f)`. Exact. I read the normal-ring node:
  its domain clause, used here, means integral closedness in the fraction field.
  Mathlib.RingTheory.IntegralClosure.IntegrallyClosed defines IsIntegrallyClosed
  using FractionRing. The inline conjunction follows the project's normal-ring
  convention and the node's mathlib_match; it is not a second definition.
- Object p, ranging over every prime of R: `p : PrimeSpectrum R`. Exact:
  PrimeSpectrum carries `asIdeal : Ideal R` and `isPrime : asIdeal.IsPrime`.
- Object R_p: `Localization.AtPrime p.asIdeal`. Exact: I read the recorded
  declaration in Mathlib.RingTheory.Localization.AtPrime.Basic, which is
  `Localization p.asIdeal.primeCompl`; the bundled prime supplies the instance.
  Residue fields and fibre rings in that dependency node are not used here.
- Definition of the subset U, no extra clause: the set comprehension requires
  `IsDomain (Localization.AtPrime p.asIdeal) ∧
  IsIntegrallyClosed (Localization.AtPrime p.asIdeal)`. Exact normal-domain clause,
  using the same meaning as the hypothesis on R_f.
- Conclusion U Zariski open in Spec R: `IsOpen` of that comprehension. Exact.
  The affine-spectrum dependency records AlgebraicGeometry.Spec; I read its
  signature and `Spec_carrier`, identifying its underlying carrier with
  PrimeSpectrum R. PrimeSpectrum.zariskiTopology defines the topology by zero
  loci as closed sets. Using the underlying space directly adds no new notion
  and needs no scheme/structure-sheaf import for this purely topological claim.

Edge cases: the zero ring is excluded by the source's domain hypothesis, exactly
as by IsDomain; consequently an empty spectrum of a zero ring is not a missing
case. There is no separately quantified scheme, index set, module, or integer n.
The comprehension and IsOpen allow empty/full subsets without a nonemptiness
hypothesis. For f a unit (including f = 1), the statement still applies; f = 0
is excluded in both source and Lean. Fields and dimension-zero domains, all
characteristics, and arbitrary ring universe u are included. No independent
small test-object universe or extra algebra/finite-type instance is present.

Independent searches (H4), with wording different from the first worker's:

- msearch.py leansearch: "openness of the integrally closed localization points
  of the spectrum of a noetherian integral domain with normal localization at
  one element". Service returned Internal Server Error; recorded unavailable,
  so no negative result is inferred from it.
- msearch.py loogle: `IsOpen, PrimeSpectrum, Localization.AtPrime`: zero hits.
- msearch.py leanfinder: "Zariski open subset consisting of primes at which a
  noetherian domain is integrally closed assuming R[1/f] integrally closed".
  Eight hits: local-global integral-closedness criteria, almost-integrality,
  Noetherian descent and Zariski main property; none states this openness claim.
- msearch.py grep: `(normal|integrally.closed).{0,40}(locus|IsOpen)|
  (locus|IsOpen).{0,40}(normal|integrally.closed)` across Mathlib. Hits concern
  normalization open immersions and topological/group normality, not this locus.
- Direct rg for `normalLocus|normal_locus|normal.*locus|locus.*normal` across
  Mathlib, WeilConjectures and the project's lean/Sheaf: the upstream
  Normalization.lean discusses normalization over an already given normal open
  locus, not openness of this set. No duplicate statement was found.
  rg of dag/lean_names_upstream.json found neither normal_locus_isOpen nor
  normalLocus.

Mismatches and repairs: no mathematical statement mismatch was found. H8 was
not satisfied by the original two-sentence proof summary: it omitted the node's
localization, specialization, depth, and associated-prime steps. I replaced it
with the complete nine-step argument and its dependency identifiers. I added
the project's copyright/license/authors header, removed the unused Pointwise
scope, and replaced the unnecessarily broad LocalProperties.IntegrallyClosed
import by IntegralClosure.IntegrallyClosed, which defines the notion used.
The theorem signature and the node's lean.statement remain unchanged, verbatim
equal. There are no definitions, hollow data, private predicates, or proofs;
the sole theorem proof is sorry. Every variable/universe is explicitly bound.

Validation: scompile.py J1 lem-weil-pbc-normal-locus-open on the revised module
compiled successfully on the server in 1.4 seconds, exit 0, with no warnings.
