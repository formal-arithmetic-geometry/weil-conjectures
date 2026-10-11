## Worker report

The module `Sheaf.RingTheory.SemilocalNormalizationDimOne` states
`integralClosure.semilocal_normalization_dim_one`, with its sole proof `sorry`.
No definitions, new nodes, dependency modules, or statement corrections are needed.

Hypothesis and conclusion correspondence:
- The commutative domain B is `(B : Type u) [CommRing B] [IsDomain B]`.
- Noetherianity is `[IsNoetherianRing B]`.
- Semilocality is `[Finite (MaximalSpectrum B)]`, exactly finitely many maximal ideals,
  following Mathlib's convention in `RingTheory/LocalProperties/Semilocal.lean`.
- Krull dimension exactly one is `(hdim : ringKrullDim B = 1)`.
- Its fraction field K is `(K : Type v) [Field K] [Algebra B K] [IsFractionRing B K]`.
  The algebra map is injective because K is the fraction field of a domain.
- B' is literally `integralClosure B K`, with its canonical ring and inclusion in K.
- Semilocality of B' is `Finite (MaximalSpectrum (integralClosure B K))`.
- The parenthesized Dedekind conditions are expanded verbatim as
  `IsNoetherianRing (integralClosure B K)`, `IsDomain (integralClosure B K)`,
  `IsIntegrallyClosed (integralClosure B K)`, and `ringKrullDim (integralClosure B K) = 1`.
  In particular the dimension is not weakened to Mathlib's Dedekind dimension-at-most-one.
- Having fraction field K is `IsFractionRing (integralClosure B K) K`, using the
  canonical subalgebra-to-ambient algebra structure, not an arbitrary isomorphism.

Dependency declarations read and used:
- def-weil-pbc-noetherian-ring: `Mathlib.RingTheory.Noetherian.Defs`, `IsNoetherianRing`.
- def-weil-pbc-krull-dimension-ring: `Mathlib.RingTheory.KrullDimension.Basic`, `ringKrullDim`.
- def-weil-pbc-integral-closure: `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`,
  `integralClosure`, imported through `IntegrallyClosed`.
- def-weil-pbc-normal-ring: `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`,
  `IsIntegrallyClosed`, and `IsDomain`. Only its normal-domain clause is required here;
  the existing Mathlib conjunction fully supplies it, so no dependency replacement is needed.
- `Mathlib.RingTheory.Spectrum.Maximal.Defs`, `MaximalSpectrum`, supplies the actual
  set of maximal ideals; `Finite` supplies semilocality without a private definition.
- `Mathlib.RingTheory.Localization.FractionRing`, `IsFractionRing`, imported through
  `IntegrallyClosed`, supplies both fraction-field conditions.

Edge cases: the zero ring is excluded by IsDomain, just as by the node. A field B is
excluded by dimension exactly one. The conclusion keeps dimension exactly one even
though Mathlib's Dedekind predicate would allow dimension zero. Local rings (one
maximal ideal), multiple maximal ideals, all characteristics, and nonfinite
normalizations are covered. No module-finiteness, Nagata, Japanese, separability, or
excellence assumption is imposed. Universes u and v are independent and explicit;
there are no auto-bound variables or universes. The canonical subalgebra carries all
ring and algebra data, and no definition contains `sorry`.

Sources: the repository's literature checkout is absent on this machine. Read the
available Stacks source copies `/home/ubuntu/c1-stacks-review/varieties.tex`, lines
7416 onward, and `algebra.tex`, lines 29753 onward: Varieties 09N2 begins with exactly
this normalization assertion; Algebra 09IG gives Noetherianity and dimension one.
The node's source field still calls these Algebra 09N2 / 034X, an existing bibliographic
fault already identified in its reviewer note. The module correctly cites Varieties
09N2 and Algebra 09IG; no mathematical statement change is involved.

Searches performed:
- msearch.py leanfinder: “The integral closure of a one dimensional semilocal
  Noetherian domain in its fraction field is a semilocal Dedekind domain”. Eight hits:
  isDedekindDomain_iff, isDedekindRing_iff, integralClosure.isDedekindDomain_fractionRing,
  DVR/localization results. None states the node; the integral-closure theorem assumes
  the base is already Dedekind and hence does not cover this hypothesis.
- msearch.py loogle: `IsSemilocalRing, IsDedekindDomain, integralClosure`. Zero hits,
  unknown identifier IsSemilocalRing.
- msearch.py leansearch: “Integral closure of a one dimensional Noetherian domain
  is Noetherian”. Service unavailable: Internal Server Error.
- msearch.py grep: `semilocal|semi.local|Krull.Akizuki`, RingTheory. Ten hits on
  local properties, Picard group, associated primes, and modules; no matching theorem.
- rg of Mathlib RingTheory for semilocal, integralClosure, IsDedekindDomain and their
  defining declarations confirmed that semilocality is expressed by Finite MaximalSpectrum.
- rg of WeilConjectures, lean/Sheaf, and dag/lean_names_upstream.json for the item id
  and the chosen declaration name found no existing matching declaration or collision.
- Concept search of WeilConjectures and lean/Sheaf for semilocal normalization and
  Krull–Akizuki found the broader AlgebraicGeometry integral-closure/fibre theorem.
  Its signature was read in full: it gives no semilocal or fraction-field conclusion
  and therefore is not the same statement. Existing FiniteIntegralConductor and
  IntegralOverringJacobsonPower modules use the same Finite MaximalSpectrum convention.

The docstring carries all three proof steps and their dependency-node identifiers.
Server compilation and delivery preflight results are recorded below after validation.

Validation: scompile.py compiled the 51-line module on the server in 1.3 seconds,
exit code 0, without warnings. deliver2.py --no-push printed OK: compilation and
preflight passed except for the independent second reading, which the second reader
will supply. Nothing was pushed.


## Second reading by K1

Read the node and its four statement dependencies independently, together with the
51-line Lean module. Verdict: exact correspondence; no mathematical mismatch and
no Lean or node edits required. No new definition nodes or dependency modules are
present or needed; there is no statement correction to audit.

Source checked directly: /home/ubuntu/c1-stacks-review/varieties.tex,
`lemma-semi-local-dimension-one-conductor` (09N2), lines 7416–7443, and algebra.tex,
`lemma-integral-closure-Dedekind` (09IG), lines 29753–29775. The former states the
normalization clause for a semilocal Noetherian domain of dimension one. Although
this section introduces Situation glue earlier, this lemma is independently
quantified and does not invoke that situation (unlike the surrounding lemmas).
The latter gives Noetherianity and explicitly proves dimension equal to one,
with no separability or module-finiteness hypothesis. The node's stale source-field
tag/document discrepancy is bibliographic only: the existing reviewer note
already identifies it, and the delivered module correctly cites Varieties 09N2
and Algebra 09IG. No unauthorized source-field change was made.

Object, hypothesis and conclusion checklist (each verdict PASS):
- Object B, a commutative domain: `(B : Type u) [CommRing B] [IsDomain B]`.
- B Noetherian: `[IsNoetherianRing B]`. Opened Noetherian/Defs.lean:196–205;
  the dependency's abbreviation is Noetherian as a module over itself, equivalently
  every ideal finitely generated, exactly the node.
- B semilocal: `[Finite (MaximalSpectrum B)]`. Opened Spectrum/Maximal/Defs.lean:
  elements are precisely an ideal and its maximality proof. Thus this is finiteness
  of the set of maximal ideals, not a choice of generators or an Artinian condition.
  LocalProperties/Semilocal.lean uses precisely this convention.
- B dimension one: `(hdim : ringKrullDim B = 1)`. Opened KrullDimension/Basic.lean:30:
  this is the supremum of strict prime-chain lengths, as the dependency states.
- Object K and its relation to B: `(K : Type v) [Field K] [Algebra B K]
  [IsFractionRing B K]`. FractionRing.lean:53 defines localization at the
  non-zero-divisors; for this domain the algebra map is injective. It introduces
  exactly the fraction field, without an additional condition on B.
- Object B': everywhere the actual subtype/subalgebra `integralClosure B K`.
  Opened IntegralClosure/Algebra/Basic.lean:216: its carrier consists of the
  integral elements and includes the image of B, exactly the dependency node.
- B' semilocal: `Finite (MaximalSpectrum (integralClosure B K))`.
- B' Noetherian: `IsNoetherianRing (integralClosure B K)`.
- B' domain: `IsDomain (integralClosure B K)`.
- B' integrally closed: `IsIntegrallyClosed (integralClosure B K)`.
  Opened IntegrallyClosed.lean:65–74: integrally closed in its FractionRing.
  This is precisely the normal-domain clause of def-weil-pbc-normal-ring;
  the other clause about arbitrary normal rings is not required here.
- B' dimension exactly one: `ringKrullDim (integralClosure B K) = 1`.
  The preceding four clauses expand the node's parenthetical Dedekind definition,
  retaining exact dimension rather than weakening it to dimension at most one.
- Fraction field of B' is the same K: `IsFractionRing (integralClosure B K) K`,
  with the canonical subtype inclusion algebra, not an unrelated field isomorphism.
- Quantification order: B with its hypotheses, K with its fraction-field structure,
  then the properties of its determined integral closure. There is no extra binder,
  scalar tower hypothesis, finite extension hypothesis, or finiteness of B' over B.

Edge cases: zero ring and empty spectrum are excluded by the source's domain
hypothesis, and fields by dimension exactly one. Local rings and any finite number
of maximal ideals are allowed. There is no arbitrary index set or integer parameter
n; n = 0 has no corresponding case. Both characteristics zero and positive are
covered. Independent explicit universes u and v allow all ring and field universes.
No scheme, nonempty choice of points, excellence, Nagata, Japanese, separability,
or normalization module-finiteness assumption occurs.

Independent searches, using different wording from the first worker:
- msearch leanfinder: “Krull Akizuki normalization of a semilocal ring has finitely
  many maximal ideals”: eight hits, including finite maximal spectrum of a field,
  local/PID criteria, and Dedekind characterizations; none is this statement.
- msearch loogle: `integralClosure, MaximalSpectrum`: zero hits.
- msearch leansearch: “Normalization of a Noetherian domain of dimension one is
  semilocal when the ring has finitely many maximal ideals”: service unavailable
  (Internal Server Error); no mathematical verdict drawn from that failure.
- Direct rg in Mathlib RingTheory/IntegralClosure and DedekindDomain for Akizuki,
  normalization, semilocal, and in all Mathlib for Noetherian/maximal-spectrum
  integralClosure combinations. Read integralClosure.isNoetherianRing and
  integralClosure.isDedekindDomain_fractionRing in DedekindDomain/IntegralClosure:
  the former assumes the base integrally closed, and the latter assumes it
  already Dedekind, so neither matches this node.
- Direct rg in WeilConjectures, lean/Sheaf and dag/lean_names_upstream.json for
  semilocal normalization, the chosen declaration name, and integralClosure with
  Noetherianity or MaximalSpectrum: no duplicate. Read the source's
  Algebra.FiniteType.finite_integralClosure signature: it requires a finitely
  generated algebra over a field and states module-finiteness, not this result.
  The landed KrullAkizukiNoetherian module is a proof ingredient about intermediate
  rings, not the bundled normalization conclusion. No new notion needs a node:
  all notions are the Mathlib notions recorded by the existing dependencies.

H5/H6/H8/H9: there is no definition to be hollow and the only theorem body is
`by sorry`. The module and theorem docstrings carry the correct source places and
blueprint id. All three proof steps match the node, including both cited nodes in
steps 1–2 and the fraction-field inclusion argument in step 3. Imports supply the
actual notions used; namespace, header, line widths, and explicit binders follow
the example. The node's lean.statement is verbatim the theorem signature.
Changes made by this reading: this independent review section only.
