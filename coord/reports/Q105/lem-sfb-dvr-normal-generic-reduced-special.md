## Worker report

The module `Sheaf.RingTheory.DvrNormalGenericReducedSpecial` states
`Algebra.normal_of_normal_generic_reduced_special`, with its entire proof `sorry`.
There are no definitions, helper theorems, new nodes, dependency repairs, or statement changes.
The node copy changes only `lean`.

The inherited BLOCKED ending concerns a stage-1 attempt to split a reviewed node again.
The current assignment is stage 2, `coord/queue.tsv` lists the item at stage 2,
and its current node has no Lean record. The stage-handoff paragraph of
`coord/brief-stage2.md` explicitly authorizes recording the Lean statement in this case.
No repair note for this item was present in the read clone.

### Hypotheses and clauses

- The base is an arbitrary commutative DVR: `(R : Type u) [CommRing R] [IsDomain R]
  [IsDiscreteValuationRing R]`. This uses the exact Mathlib match of
  `def-sc-discrete-valuation-ring`, whose definition and uniformizer equivalence were read.
- The uniformizer is `(pi : R)` with
  `hpi : IsLocalRing.maximalIdeal R = Ideal.span {pi}`. This is exactly the definition
  in the node, not a stronger choice of uniformizer or of a valuation.
- The commutative finitely generated R-algebra is `(T : Type v) [CommRing T]
  [Algebra R T] [Algebra.FiniteType R T]` (the signature writes `FiniteType` inside
  `namespace Algebra`). The universes of R and T are independently bound.
- Flatness as an R-module is `[Module.Flat R T]`. It is the recorded dependency
  declaration, equivalent to flatness of the algebra map; faithful flatness is not assumed.
- The generic algebra `T_L = T[1/pi]` is the canonical
  `Localization.Away (algebraMap R T pi)`. The node already explicitly identifies
  the generic tensor product with this algebra. Choosing this canonical fraction
  construction does not require a new object, equivalence, or arbitrary map.
  The fraction field L is uniquely determined by R up to canonical R-isomorphism;
  it has no independent role in the statement after the node's displayed identification.
- Generic normality is `hgeneric`, quantifying over EVERY prime ideal p of that
  localization and asserting `IsDomain (Localization.AtPrime p)` AND
  `IsIntegrallyClosed (Localization.AtPrime p)`. This is precisely the inline normal-ring
  form recorded by `def-weil-pbc-normal-ring`, including both parts of normal domains.
- The residue field k is R/pi R; the special algebra is written directly as
  `T ⧸ Ideal.span {algebraMap R T pi}`. This is the node's T/pi T, canonically the
  base change to k. No independent residue-field parameter or assumption is needed.
- `hspecial : IsReduced (T ⧸ Ideal.span {algebraMap R T pi})` says there are no nonzero
  nilpotents, exactly as the node defines reducedness.
- The first conjunct of the conclusion quantifies over all prime ideals of T and
  asserts the same domain-and-integrally-closed conjunction for their localizations.
  This is normality of T, including rings with zero divisors and the zero ring.
- The second conjunct, `Function.Injective (algebraMap T
  (Localization.Away (algebraMap R T pi)))`, explicitly states the injectivity of
  the canonical localization map referred to in the node.
- The final conjunct quantifies over every element z of the same generic algebra.
  `IsIntegral T z` means it satisfies a monic polynomial with coefficients in T;
  the conclusion `∃ a : T, algebraMap T (...) a = z` says exactly that z belongs to T
  under the injective map. It does not replace this by integrality over R.
- No normality of the special fibre, geometric normality or reducedness, nonemptiness,
  excellence, completeness, algebra-domain assumption, or characteristic restriction is added.

### Dependency declarations and imports

Statement dependencies (public imports):

- `Mathlib.RingTheory.DiscreteValuationRing.Basic`: `IsDiscreteValuationRing`;
  `IsDiscreteValuationRing.irreducible_iff_uniformizer` confirms the uniformizer encoding.
- `Mathlib.RingTheory.RingHom.Flat`: `RingHom.Flat` and `Module.Flat`, as recorded by
  `def-weil-pbc-flat-ring-map`. The class signature and tensor-injectivity characterization
  in `Mathlib.RingTheory.Flat.Basic` were read too.
- `Mathlib.RingTheory.IntegralClosure.IntegrallyClosed`: `IsIntegrallyClosed`,
  `IsIntegrallyClosedIn`, and the integral-element interpretation.
- `Mathlib.RingTheory.Localization.AtPrime.Basic`: `Localization.AtPrime`, for the exact
  inline normality predicate from `def-weil-pbc-normal-ring`.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType`.
- `Mathlib.RingTheory.Localization.Away.Basic`: canonical localization at powers of pi.
- `Mathlib.RingTheory.Ideal.Quotient.Nilpotent`: the special-fibre quotient and reducedness.

Already stated proof dependencies (plain imports, as required by stage 2):

- `Mathlib.Algebra.Module.LocalizedModule.Basic`: `LocalizedModule`, the recorded
  localization construction; the source checks its ring specialization agrees reducibly
  with `Localization`.
- `Mathlib.RingTheory.IntegralClosure.Algebra.Basic`: `integralClosure` and `IsIntegral`;
  the signature and monic-polynomial docstring of `IsIntegral` were read in
  `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs`.
- `Mathlib.RingTheory.Spectrum.Maximal.Localization`:
  `PrimeSpectrum.toPiLocalization_injective`.
- `Mathlib.RingTheory.FiniteType`: `Algebra.FiniteType.isNoetherianRing` (already public
  because finite type occurs in the statement).
- `Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian`:
  `minimalPrimes.finite_of_isNoetherianRing`.
- `Mathlib.RingTheory.Noetherian.Defs`: `IsNoetherianRing`.
- `WeilConjectures.RingTheory.NormalRingIntegrallyClosedTotal`:
  `integral_totalFraction_mem_range_of_normal`.
- `WeilConjectures.RingTheory.ReducedNormalIffIntegrallyClosedTotalFractions`:
  `reduced_normal_iff_integrallyClosed_totalFractions`.

I read the full signatures and docstrings of the statement-dependency declarations,
and the signatures of these proof tools. The theorem docstring carries all six steps
of the accepted proof, including the fraction-map construction and its injectivity.
No proof is supplied in this stage-2 module.

### Sources and edge cases

I opened [Prasad--Yu, Appendix Remark A.3, printed p.27]
(https://arxiv.org/pdf/math/0405381), including the paragraph about Serre criteria.
It asserts normality for a finite-type flat scheme over a normal Noetherian domain
with normal generic fibre and reduced other fibres. Over a DVR this is exactly the
normality assertion here. The additional image clause is the accepted node's
least-denominator argument, generalized from Stacks Tag 055J; normality is recovered
using the existing Tags 034M and 030C tools. No correction or dispute was found.

Checked before writing: T=0 is permitted because there is no `Nontrivial T` or
`IsDomain T`; there are no prime ideals, and both image assertions hold in the zero
ring. An empty special fibre means the displayed quotient is zero, which is reduced;
pi then becomes a unit and the localization is T itself. Products such as R x R are
permitted: normality does not mean T is a domain. Reduced singular special fibres
are permitted: `hspecial` asks only for `IsReduced`. Arbitrary residue characteristic
is permitted. The generic algebra also need not be a domain. The monic-integral
clause includes elements satisfying equations of degree one. Flatness, finite type,
and generic normality remain hypotheses even though the least-denominator portion
alone uses fewer of them.

As hypothesis sanity checks, over a characteristic-zero DVR the algebra
R[x]/(x^2-pi^2) has a normal generic fibre but a nonreduced special fibre; x/pi is
integral in the generic algebra without lying in the model. Dropping flatness allows
R[x]/(pi*x), for which the localization map is not injective. Neither omitted hypothesis
is being smuggled into a definition or replaced by a tautology.

### Searches

All searches were read-only and preceded writing the Lean module.

- `msearch.py ... leanfinder`: "A flat finite type algebra over a discrete valuation ring
  with normal generic fibre and reduced special fibre is normal". Eight hits concerned
  good reduction, normalization, the DVR TFAE, valuative squares, and geometric reducedness;
  none states this criterion or its integral-element clause.
- `msearch.py ... loogle`: `IsDiscreteValuationRing, IsIntegrallyClosed`.
  The only hit was `IsDiscreteValuationRing.TFAE`, about the base ring itself.
- `msearch.py ... grep`: `normal.*reduced|reduced.*normal|generic.*normal` in `RingTheory`.
  The only hit was an implementation note in `IntegralClosure/IntegrallyClosed.lean`.
- `rg` in `lean/WeilConjectures` and `lean/Sheaf` for DVR/normal and
  normal/generic/reduced terminology found related curve and normalization material,
  but no full statement. The narrower query
  `normal.*generic.*reduced|reduced.*special.*normal|normal_generic_reduced_special`
  returned no match.
- `grep -rn` for the exact node id in `lean/WeilConjectures` returned no match.
- The selected new full declaration name was also searched in both library roots
  and `dag/lean_names_upstream.json`; there was no prior declaration.

### Validation

`scompile.py Q105 lem-sfb-dvr-normal-generic-reduced-special` compiled the delivered
module cleanly against the published server build in both sandbox and library modes
(1.7 s and 1.4 s). No errors or unexpected warnings were printed. All variables and
universes are explicitly bound; no diagnostic commands, local notation, local
instances, or private definitions remain. Each Lean line is at most 100 characters.
Delivery dry-run and push are performed with the prescribed `deliver2.py` wrapper.

## Second reading by Q105

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
