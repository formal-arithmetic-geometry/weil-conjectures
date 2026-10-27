## Worker report

The module `Sheaf.RingTheory.AdicNormalCompletionLifting` states
`AdicCompletion.normal_atPrime_of_isQuasiExcellent_quotient`, with proof `sorry`.
It adds no definition or auxiliary theorem and changes only the item's `lean` record.
No statement correction or disputed statement is needed.

Hypothesis and conclusion correspondence:

- The commutative ring is `(A : Type u) [CommRing A]`, with arbitrary explicitly bound universe `u`.
- Noetherianity is `[IsNoetherianRing A]`.
- A normal domain is `[IsDomain A] [IsIntegrallyClosed A]`, exactly the recorded normal-domain
  clause of `def-weil-pbc-normal-ring`.
- The ideal is `(I : Ideal A)`; no properness, principal-generation, or maximality assumption is added.
- Completeness is `[IsAdicComplete I A]`, including separatedness, hence bijectivity of the
  canonical map to `AdicCompletion I A`.
- Quasi-excellence of the closed fibre is `(hquot : IsQuasiExcellent (A ⧸ I))`.
  This uses the existing predicate, including its Noetherian, G-ring, and J-2 clauses.
- Every prime is represented by `(p : Ideal A) [p.IsPrime]`, with no containment condition on `I`.
- The displayed completion is `AdicCompletion (IsLocalRing.maximalIdeal (Localization.AtPrime p))
  (Localization.AtPrime p)`. The localization's maximal ideal is `p A_p`, by
  `Localization.AtPrime.map_eq_maximalIdeal`. Mathlib's completion is the compatible sequences
  in the quotients by powers of this ideal, including the harmless zero-th quotient.
- The conclusion's three conjuncts are `IsDomain`, `IsLocalRing`, and `IsIntegrallyClosed` of
  that very completion. Together they express exactly a normal local domain.
- No `IsUniversallyCatenary A`, `IsExcellent A`, or `IsGRing A` hypothesis occurs.

Statement dependencies and declarations read and used:

| Node | Module | Declaration |
| --- | --- | --- |
| def-exc-excellent-ring | Sheaf.RingTheory.ExcellentRing | IsQuasiExcellent |
| def-weil-pbc-adic-completion | Mathlib.RingTheory.AdicCompletion.Basic, with ring structure from Algebra | AdicCompletion |
| def-weil-pbc-adically-complete-ring | Mathlib.RingTheory.AdicCompletion.Basic | IsAdicComplete |
| def-weil-pbc-localization-at-prime | Mathlib.RingTheory.Localization.AtPrime.Basic | Localization.AtPrime |
| def-weil-pbc-noetherian-ring | Mathlib.RingTheory.Noetherian.Defs | IsNoetherianRing |
| def-weil-pbc-normal-ring | Mathlib.RingTheory.IntegralClosure.IntegrallyClosed | IsIntegrallyClosed, IsDomain (normal-domain form) |

The definition signatures and docstrings were read in these modules. The upstream
`WeilConjectures.RingTheory.GRing` source was also read to check the quotient predicate's
formal-fibre meaning. The withdrawn CompactObject example was checked against its current node,
which now points to `WeilConjectures.CategoryTheory.CompactObject`; the upstream example was read.

Proof imports follow the recorded plan: `Sheaf.RingTheory.QuasiExcellentNagata`
(`isNagataRing_of_isQuasiExcellent`); `WeilConjectures.RingTheory.GRing` (`IsGRing`);
`WeilConjectures.RingTheory.RegularRingNormal` (`IsRegularRing.isNormalRing`);
`WeilConjectures.RingTheory.AdicCompletionNoetherian` (`AdicCompletion.isNoetherianRing`);
`WeilConjectures.RingTheory.NormalOfFlatNormalFibers`
(`RingHom.normal_of_flat_normal_fibers`). Mathlib proof imports supply
`IsLocalization.isNoetherianRing`, `isIntegrallyClosed_of_isLocalization`,
`IsFractionRing.isFractionRing_of_isLocalization`, completion locality and faithful flatness.
The proof-only node `lem-per-nagata-normal-formal-fibres-lifting` currently has neither a Lean
record nor Mathlib match, so there is no module for it to import. Its statement is only used in
this theorem's natural-language proof plan, not in the Lean signature; it has not been restated.

Source read: Kurano–Shimomoto, *Ideal-adic completion of quasi-excellent rings (after Gabber)*,
Theorem 5.1 Step 1 (1-4), printed p. 8, equation (5.3), printed p. 9, and Appendix A's lifting
property. The statement and five proof steps in the DAG were read. The docstring retains the
quotient Nagata/formal-fibre preparation, lifting on the original pair, localization and flat
completion facts, flat normal ascent, and the final local-ring identification. It does not
assume that localization preserves completeness, or invoke quasi-excellence lifting downstream.

Edge cases checked before writing: at `p = 0`, the localization is a field and completion along
its zero maximal ideal gives that field; a zero prime is not excluded. At `I = 0`, completeness
is automatic and the quotient is `A`, so the expected quasi-excellent case is retained. At
`I = A`, completeness forces the ring to be zero, incompatible with `IsDomain`; no artificial
proper-ideal binder is needed. The zero ring is already excluded by the stated domain
hypothesis. No dimension bound, localness of `A`, containment `I ≤ p`, or restriction on residue
characteristic is imposed. All rings and completion types live in `Type u`; there is no smaller
universe of test algebras or extra universe equality.

Searches actually run for an existing statement:

- `msearch.py`, LeanFinder: "A normal Noetherian domain complete along an ideal with quasi
  excellent quotient has normal local completions". Eight hits: Dedekind valuation completions,
  henselian completeness, almost integral closure, and locality of an already complete ring;
  none states this theorem.
- `msearch.py`, Loogle: `"IsAdicComplete", "IsIntegrallyClosed"`. Zero hits.
- `msearch.py`, Mathlib grep:
  `normal.*completion|completion.*normal|IsAdicComplete.*IsIntegrallyClosed|isIntegrallyClosed.*[Cc]ompletion`.
  Zero hits.
- `rg` in both project source trees with
  `normal.*completion|completion.*normal|adic.normal|isIntegrallyClosed.*[Cc]ompletion`
  (case insensitive): unrelated normalized-completion comparisons and the separate
  curve-normalization/completion theorem; no match for this ring-theoretic statement.
- `rg` for `lem-per-adic-normal-completion-lifting` in `lean/WeilConjectures`: no hit.
- `rg` in both project source trees and `dag/lean_names_upstream.json` for a candidate theorem
  name: no collision. The final namespace/name is also checked by server compilation/preflight.

Validation: the delivered module was compiled through `scompile.py` in module mode against the
published live library; sandbox and library compiles both succeeded (1.9 seconds each), with
no errors or non-sorry warnings. All variables and universes are bound explicitly using
`set_option autoImplicit false`; maximum Lean line width is below 100. The only proof is the
required `sorry`.

## Second reading by Q121

No second reading by a worker: since 2026-10-17 the worker delivers directly and the maintainer's independent review is the only review.
