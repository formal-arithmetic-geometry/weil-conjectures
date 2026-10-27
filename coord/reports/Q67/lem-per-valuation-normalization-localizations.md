## Worker report

The module `Sheaf.RingTheory.ValuationNormalizationLocalizations` states
`ValuationSubring.normalization_localizations`, with one `sorry` and no other postponed
proof. Its helper `ValuationSubring.normalizationLocalization` specializes the existing
Mathlib `Localization.subalgebra.ofField` to the integral closure and a maximal ideal.
It supplies real canonical data, using the already proved
`integralClosure.isFractionRing_of_finite_extension`; it neither chooses a prolongation
nor assumes an unproved existence theorem. This helper belongs to the localization
already named in this node, so it introduces no independent notion or new DAG node.

Hypothesis and clause correspondence:

- The fields K and L are `{K : Type u} {L : Type v} [Field K] [Field L]`, with explicitly
  bound independent universes, and their inclusion is `[Algebra K L]` and `algebraMap K L`.
  A unital homomorphism of fields is injective. `[FiniteDimensional K L]` states exactly
  a finite field extension and hence includes algebraicity, without separability.
- The given valuation ring V inside K with fraction field K is `(V : ValuationSubring K)`.
  This Mathlib structure has the membership-or-inverse-membership property in K and
  instances `ValuationRing V` and `IsFractionRing V K`. It packages exactly both parts
  of the node's input, rather than an abstract valuation domain with unspecified field.
- The normalization C is always `integralClosure V L`. The induced V-algebra of L is
  the restriction of scalars along V's inclusion in K. Mathlib defines the carrier
  by `IsIntegral V x`, literally roots of monic polynomials over V.
- Nonzero and integral domain are `Nontrivial (integralClosure V L)` and
  `IsDomain (integralClosure V L)`. Integrality over V is
  `Algebra.IsIntegral V (integralClosure V L)`; fraction field L is
  `IsFractionRing (integralClosure V L) L`.
- Nonempty set of maximal ideals is `Nonempty (MaximalSpectrum (integralClosure V L))`.
  `MaximalSpectrum` consists exactly of an ideal with its maximality proof.
- Every maximal ideal n is quantified as `n : MaximalSpectrum (integralClosure V L)`.
  The subring C_n inside L is `(V.normalizationLocalization n).toSubring`.
  `Localization.subalgebra.ofField` has carrier precisely the fractions c/s with
  c,s in C and s outside n, and Mathlib provides its `IsLocalization` instance.
  It is therefore the recorded `Localization.AtPrime n.asIdeal` represented in L,
  using the canonical localization map, not an abstract isomorphic ring with an
  arbitrary embedding. The theorem says `ValuationRing (V.normalizationLocalization n)`.
- Its intersection with K is the exact subring equality
  `(V.normalizationLocalization n).toSubring.comap (algebraMap K L) = V.toSubring`.
- Every W in the converse is `W : ValuationSubring L`, which includes fraction field L.
  Restriction to V is `W.comap (algebraMap K L) = V`. The conclusion is `∃! n` over
  the full maximal spectrum, with `W.toSubring = (V.normalizationLocalization n).toSubring`.
  Equality is inside L. Proof irrelevance ensures uniqueness here is precisely that
  of the underlying maximal ideal, not of a selected maximality certificate.
- The signature includes no henselian, Noetherian, separability, rank, or module-finite
  condition on C/V. The only finiteness condition is the original finite extension L/K.

Dependency declarations read and used:

- `def-pc-field-extension`: `Algebra`, `Mathlib.Algebra.Algebra.Defs` (full class and
  docstring read at lines 95ff). It is used with fields, as the record specifies.
- `def-trf-valuation-ring`: its Mathlib match is `ValuationRing; ValuationRing.TFAE`,
  `Mathlib.RingTheory.Valuation.ValuationRing`. The domain class at lines 62ff and
  TFAE at lines 407ff were read. `Mathlib.RingTheory.Valuation.ValuationSubring`
  packages the ambient-field version and supplies the valuation-ring and fraction-field
  instances at lines 124 and 153; its definition, instances, and comap were read.
- `def-weil-pbc-integral-closure`: `integralClosure` in
  `Mathlib.RingTheory.IntegralClosure.Algebra.Basic` (lines 216ff), and `IsIntegral`
  in `Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs` (lines 50ff).
- `def-weil-pbc-localization-at-prime`: `Localization.AtPrime`,
  `Mathlib.RingTheory.Localization.AtPrime.Basic` (lines 50ff). Its existing concrete
  realization `Localization.subalgebra.ofField` and its `isLocalization_ofField`
  instance were read in `Mathlib.RingTheory.Localization.AsSubring` (lines 120ff).
  The proof needed to use the construction is the proved
  `integralClosure.isFractionRing_of_finite_extension` in
  `Mathlib.RingTheory.Localization.Integral` (lines 426ff), also read in full.
- `MaximalSpectrum` in `Mathlib.RingTheory.Spectrum.Maximal.Defs` is the existing
  bundled type of maximal ideals, not a newly defined notion.
- The sole proof dependency `lem-trf-valuation-normalization-localizations` has no
  `lean`, `mathlib_match`, or recorded finished declaration. Its whole statement and
  nine proof steps were read. It is not needed to TYPE this statement, so no duplicate
  theorem or module is introduced for it and no nonexistent proof import is invented.
  The docstring gives the item's complete one-step proof plan by reuse of that node.
  The maintainer can add its proof-only import when that node receives a module,
  as stages/2-statements.md section 3 rule 7 prescribes.

Sources and repair handoff: read the resolved stage-1 repair note for this item,
`coord/changes/20261024-Q112-strict-completion-inputs.md`, the current reviewed split,
and the current blueprint ancestor's statement and proof, plus its unit section in
`literature/blueprint/latest/`. The admitted stage-1 split and all non-Lean node fields
are preserved. The ILO PDF was read through `pdftotext`: XX 4.4, printed p.374, gives
only the dense henselian valued-field context and the Bourbaki VI section 8 Krasner
reference. The report/module do not attribute the whole normalization theorem to ILO.
The local Stacks `algebra.tex` valuation-ring section, especially `lemma-dominate`
(00IA), `lemma-valuation-ring-normal` (00IC), and the inverse dichotomy were read.
The independently reconstructed normalization theorem is the accepted proof dependency.
No excluded completion comparison, excellence assumption, or SGA source is used.

Edge cases checked before drafting:

- L=K gives C=V and its unique maximal localization V. Both the field case and
  nonfield valuation rings are included.
- V=K gives C=L, maximal ideal zero, localization L, and only prolongation L.
  Thus neither nonempty maximal spectrum nor the converse excludes trivial valuations.
- Purely inseparable finite extensions satisfy the same `FiniteDimensional` binder;
  there is no `IsSeparable` or perfection assumption.
- Higher-rank and non-Noetherian valuation rings are allowed by `ValuationSubring`;
  no discrete valuation or numerical value group is introduced.
- Non-module-finite integral closure is allowed; `Algebra.IsIntegral` is not
  `Module.Finite`. Zero is integral, and the valuation dichotomy at zero is harmless
  since every subring contains zero.
- The converse's specified fraction field L is essential. An abstract subring
  valuation domain with smaller fraction field would not suffice; using
  `ValuationSubring L` retains the node's explicit correction.
- Universes u and v are independent and explicitly declared. There is no independent
  test universe causing a vacuous hypothesis and no restriction on characteristic.

Searches performed on 2026-10-24:

1. `msearch.py ... leanfinder` query: “The integral closure of a valuation ring in a
   finite field extension has valuation localizations at maximal ideals and these
   classify all prolongations”. Eight hits, including `Valuation.HasExtension`
   contraction lemmas, `Valuation.Integers.integrallyClosed`, and the discrete
   `IsDiscreteValuationRing.map_algebraMap_eq_valuationSubring`. None states the
   normalization/prolongation theorem for an arbitrary valuation ring.
2. `msearch.py ... loogle 'ValuationSubring, integralClosure'`: six hits, including
   `iInf_valuationSubring_superset`, `ValuationSubring.equiv`, and integrality and
   injectivity lemmas. Their defining sources were read; none classifies maximal
   localizations or all prolongations.
3. `msearch.py ... grep 'integralClosure|localization' RingTheory/Valuation`: 25 hits,
   including the integral-closedness, discrete-valued algebra instances, and localization
   of an already given valuation ring. The relevant full declarations in Integral.lean,
   AlgebraInstances.lean, LocalSubring.lean and ValuationSubring.lean were read.
4. `msearch.py ... leansearch` query: “Prolongations of a valuation ring to a finite
   algebraic extension are the localizations of its integral closure”. Eight hits:
   extension compatibility and integrally-closedness/intersection results, no exact match.
5. `rg` in `lean/WeilConjectures`, `lean/Sheaf`, and `dag/lean_names_upstream.json`
   for normalization/prolongation names, valuation plus integralClosure, and the node ids;
   and the prescribed `grep -rn` of this item's id in WeilConjectures. No exact existing
   theorem. Upstream `HenselianDVRExtension` has stronger DVR/henselian assumptions.
   `RingTheory.normalizationLocalizationMap` in NormalizationIntegralClosureKrull
   is a general map to `FractionRing A`, not the normalization/prolongation theorem
   or the localization subalgebra inside L; the existing Mathlib subalgebra is reused.
6. `rg` in Mathlib Localization found the canonical existing `subalgebra.ofField`
   and `integralClosure.isFractionRing_of_finite_extension`, reused instead of recreating
   localization fractions or proving a helper theorem.

No statement correction, new node, or dependency record repair is needed.
No unresolved STATEMENT-DISPUTED issue was found.

Validation: prescribed `scompile.py Q67 lem-per-valuation-normalization-localizations`
compiled the sandbox and named library module cleanly (21.0 s and 1.6 s respectively).
Only the stage-2 theorem proof is postponed. `deliver2.py --no-push` printed
`OK (dry run): commit 82aedbb79ce passes the preflight and compiles; nothing pushed`.
The final report corrects the name of the inspected Krull-normalization map to
`RingTheory.normalizationLocalizationMap`; there is no mathematical or Lean change.
The delivery wrapper repeats its normal checks before pushing.

## Second reading by Q67

This is a second pass by the same worker, not an independent second agent: the dispatcher
explicitly forbids starting agents, and the maintainer independently reviews delivery.
I reopened the node, dependency records and resulting module and compared the input
fields, V and its fraction field, literal monic-polynomial closure, all four ring/field
properties, nonempty maximal spectrum, both localization properties, and the converse
with uniqueness. Each appears in the correspondence list above. In particular, the
converse's `ValuationSubring L` retains its specified fraction field; the forward
contraction uses the canonical map K→L; and maximal ideals are not replaced by all primes.
The helper introduces no stronger hypothesis: its finite-dimensional assumption is
exactly the item's field-extension assumption, and its fraction-field proof is already
in Mathlib. No mismatch or mathematical statement change was found. The definition
contains no `sorry`, no unproved arbitrary data is chosen, and every universe/variable
is explicitly bound. The final cosmetic change added the standard copyright header.
