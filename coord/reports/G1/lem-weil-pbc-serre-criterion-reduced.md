# Worker report: lem-weil-pbc-serre-criterion-reduced

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-serre-criterion-reduced.json`: split the equivalence into the two directions of Stacks Algebra 031R, including the reverse height induction.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-localization-preserves-reduced.json`: Mathlib leaf for a prime localization, `instIsReducedLocalization` (`RingTheory/LocalProperties/Reduced.lean:47`).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-prime-localizations-jointly-injective.json`: Mathlib leaf, `PrimeSpectrum.toPiLocalization_injective` (`RingTheory/Spectrum/Maximal/Localization.lean:172`).
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-primes-of-localization.json`: Mathlib leaf, `IsLocalization.AtPrime.orderIsoOfPrime` (`Localization/AtPrime/Basic.lean:145`) and `IsLocalization.orderIsoOfPrime` (`Localization/Ideal.lean:236`), one per clause.
- `dag/nodes/sec-proper-base-change/lem-weil-pbc-localize-localization-at-prime.json`: Mathlib leaf, `IsLocalization.localizationLocalizationAtPrimeIsoLocalization` (`Localization/LocalizationLocalization.lean:156`), once per clause.

## Sources and mathematical checks

I read `algebra.tex` lines 43872-43973, especially Tag 031R (`lemma-criterion-reduced`), and checked Tags 00EU, 00HN, 00E3, 00LL, 00LD and 04KN against `tags/tags`. The item statement agrees with 031R and the existing `def-weil-pbc-serre-conditions-rk-sk`. The first implication uses 00EU for height-zero localizations; for a positive-dimensional reduced local ring an associated maximal ideal would annihilate a nonzero nonunit element in the maximal ideal, giving a nonzero square-zero element. The existing 00LL node then gives a nonzerodivisor and hence depth at least one. The converse follows 031R's induction on finite prime height: the depth condition supplies a regular element $t$ of $R_{\mathfrak p}$; each prime localization of $(R_{\mathfrak p})[1/t]$ is $R_{\mathfrak q}$ for a strictly smaller prime $\mathfrak q$, hence reduced by induction. Injection into the product of prime localizations makes the principal localization reduced; the regularity of $t$ embeds $R_{\mathfrak p}$ in it; a final product injection gives reducedness of $R$.

For the small cases: the zero ring has no primes and both sides hold; a field is the height-zero base case; the dual numbers $k[\varepsilon]/(\varepsilon^2)$ fail $(R_0)$; $k[x,y]/(x^2,xy)$ has a reduced minimal localization but fails $(S_1)$ at $(x,y)$ because $x$ is a nonzero socle element. For the new leaves, localization at a nilpotent element gives the zero ring and an empty prime set; localization at a unit leaves the prime set unchanged. These do not contradict their statements.

Before creating nodes I searched the current DAG by `031R`, `00HN`, `00E3`, `localization.*reduced`, `product.*localizations`, and prime-localization concepts. The existing 00EU, 00LL, finite-height, and height-chain nodes were cited. No existing node states the four new leaf facts. LeanSearch, LeanFinder or Loogle, and Mathlib source searches were recorded for each new node. All Mathlib declarations and cited lines were read.

## Attachments

None. The item has `lean_audit.slopmaster2.state = none`.

## WANTED

None.

## Earlier material

The imported item had no proof steps. The Stacks proof leaves the prime correspondence, iterated localization, and injectivity into the product of localizations implicit or by reference; the split records them as exact Mathlib leaves. No source statement changed. The composition of two prime correspondences and two iterated-localization equivalences is explicit in Step 4 of the item. The DAG defines prime localization and localization away from one element, so the new leaves state only those cases and cite those genuine definitions. The general ring multiplication of $S^{-1}R$ is not defined in `def-weil-pbc-module-localization`. The reducedness consequence of joint injectivity is one line from the exact Mathlib theorem applied to a nilpotent element.

## Verification and remaining work

`python3 tools/review_split.py lem-weil-pbc-serre-criterion-reduced` passes (four new nodes). `python3 tools/check_dag.py --cycles` reports zero cycles and seven unrelated reachability warnings for other existing nodes, so its exit code is 1. No Lean code was written or built. The new leaves need the lead's independent B8 review before delivery.
## Review by G1

I read Algebra Lemma 031R (`lemma-criterion-reduced`) in `algebra.tex:43935-43973`, including its uses of 00EU, 00LL/00LD, 00E3, and 00HN. The item's Noetherian hypothesis and the meanings of R_0 and S_1 agree with the source and with `def-weil-pbc-serre-conditions-rk-sk`. Step 1 applies the existing minimal-prime field statement to height-zero primes, then the regular-local definition in dimension zero. Step 2 uses localization of reduced and Noetherian rings, rules out the maximal ideal as an annihilator in a positive-dimensional reduced local ring by a nonzero square-zero element, and applies the existing nonzerodivisor criterion and depth definition. Each cited statement gives the fact used.

For the converse, step 3 cites the accepted finite-dimension node for Noetherian local rings and sets up induction on finite prime height; the height-zero case is a field by R_0. In step 4, S_1 gives a regular element t in the maximal ideal, hence an injection into the principal localization. The prime correspondence and iterated-localization leaves identify every prime localization there with R_q for q properly below p; the cited height-chain node gives height(q)<height(p). Step 5 uses the exact product-injectivity leaf to deduce reducedness of the principal localization and then of R_p and R. The induction is well-founded and uses no assertion from a cited node's proof.

The four new nodes are statement-only, self-contained, and now cite genuine definitions for the localization forms they use. I checked `instIsReducedLocalization` at `Reduced.lean:47`, `PrimeSpectrum.toPiLocalization_injective` at `Spectrum/Maximal/Localization.lean:172`, `IsLocalization.AtPrime.orderIsoOfPrime` at `Localization/AtPrime/Basic.lean:145`, `IsLocalization.orderIsoOfPrime` at `Localization/Ideal.lean:236`, and `IsLocalization.localizationLocalizationAtPrimeIsoLocalization` at `LocalizationLocalization.lean:156`. These are exact or the stated one-line prime/principal specialization; the reducedness corollary of product injectivity is one immediate nilpotent calculation. I searched the DAG for these localization and product facts; the existing 00EU, 00LL, and height nodes were reused. I sent back B3 because two leaves initially had no citation and used general ring localization, for which the DAG has no definition; the worker narrowed them to the prime/principal cases actually needed. I checked the zero ring, fields, dual numbers, and an embedded-prime example. No other-unit route exception or source statement change is involved; the DAG has zero cycles.
