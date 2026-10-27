# lem-sfb-parameter-root-boundary-dvrs — N8

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-parameter-root-boundary-dvrs.json`: item, statement, split into eleven steps. The statement and existing provenance are retained. Mathlib searches found individual ingredients, but no declaration giving the simultaneous parameter-root presentation and finite boundary localization identification.
- `citations.json`: fourteen step/node citations, each a verbatim substring of the current cited statement.
- `report.md`: this report and signed mathematical review.

New nodes: 0. New Mathlib leaves: 0. No unit record was changed: this auxiliary item is not its unit's key node. The sandbox also contains the search command's `searches.jsonl` and the local JSON-writing script.

## Attachments

None for the item. Searched `lean/WeilConjectures/` for the exact blueprint tag and for parameter-root and boundary-DVR terminology. The boundary-related hit in AffineUnitDivisorBaseChange does not state this item. Existing public `IsLocalization.regular_principal_prime_dvr` in `lean/WeilConjectures/RingTheory/RegularPrincipalPrimeLocalizationDvr.lean:102` gives the already recorded node `lem-sbc-regular-principal-prime-localization-dvr`; it is used as a tool, not asserted to finish the present item. Its statement and displayed proof were read.

## WANTED

None. The source PDF and supporting Stacks source files are present.

## Corrections and route

No statement dispute was found. The statement has henselianity but does not require n to be invertible, and the split retains that generality. ILO IX Proposition 2.1 works with n invertible for its Kummer geometry; our use of that document is its root-algebra presentation only. General henselian root-algebra regularity is the separate, existing node `lem-sfb-henselian-parameter-root-regularity`, which explicitly allows every n>0. The proof origin is marked agent: ILO does not explicitly prove this entire boundary-local algebra statement.

The item has no imported blueprint ancestor. `tools/blueprint_refs.py ancestor` reports None; its existing null `from.node`, precise place, and full via list are preserved. Searches of all blueprint nodes for `parameter-root`, `regular system parameters`, `localization integral`, `00NQ`, and `boundary`, together with DAG searches by the root algebra, the relevant Stacks tags and localization/finite-algebra terminology, found no blueprint statement of the complete item. Existing generic algebra nodes were reused throughout. The contextual current blueprint direct-images proof (3) was read: this is an auxiliary boundary calculation supporting its coefficient-specific open-direct-image input, and no higher route was changed. There are no new nodes requiring duplicate comparisons.

Two generic tools are explicitly declared in `split_report.tool_uses`: regular parameter quotients (`lem-weil-pbc-regular-local-generators-regular-sequence`) and principal-prime DVR localizations (`lem-sbc-regular-principal-prime-localization-dvr`). Neither replaces a geometric step of the unit. The other off-unit algebra tools are Mathlib leaves or a recorded closed node.

## Not duplicates

No new nodes. All ingredient statements are existing DAG nodes, including the exact parameter-quotient theorem, the principal-prime DVR localization theorem, finite algebra integrality, maximal ideal contraction, and the finite-dimensional-domain field criterion.

## Review by N8

I read ILO, *Travaux de Gabber*, Exposé IX Proposition 2.1(i), proof on printed pp.133–134 (PDF pp.139–140). It displays the simultaneous parameter-root algebra in the strict-local SNC setting. The PDF's subsequent Kummer equivalence and its SGA citation are not used by this algebraic split. For the algebra I read Stacks `algebra.tex`, Tags 00NP (`lemma-regular-domain`), 00NQ (`lemma-regular-ring-CM`), 00PD (`lemma-characterize-dvr`), 00CT (`proposition-localize-quotient`), 00E3 (`lemma-spec-localization`), 00GK (`lemma-finite-is-integral`), 00GS (`lemma-integral-over-field`), and 00OI (`lemma-going-up-maximal-on-top`). The monic quotient basis is the existing 04GG node, whose statement, source and Mathlib match I read. No new source lemma was introduced.

For step 1 I opened `lem-sfb-henselian-parameter-root-regularity` and checked its statement supplies all used data: monomial freeness, injectivity, Noetherianity, regular locality and domain property, and the full parameter system in B. Its hypotheses are exactly the present ring hypotheses and n>0, not invertibility of n. The original ring is also a domain because its map into this domain is injective.

For step 2 I opened `lem-weil-pbc-regular-local-generators-regular-sequence`. Its statement includes regular quotients of every parameter prefix, their dimensions, and regularity after every permutation. Putting the chosen parameter first therefore gives both nonzerodivisors and both regular local quotients. I opened `lem-sc-regular-local-domain`, which says exactly that a regular local ring is a nonzero domain; it applies to these two quotients. Thus neither primality assertion uses normality or an unstated excellence assumption. Step 3 is the explicit presentation map and its inverse, verified on all generators; n>0 is needed when setting x_i=0.

For step 4 I read `lem-weil-pbc-monic-quotient-free`: it supplies a monomial basis for a monic one-variable quotient over any commutative coefficient ring. Iteration is legitimate over the successive root algebras. Product bases give the stated basis of B/(x_i); the surviving coefficient of the basis vector 1 proves injection and the precise contraction of (x_i). No contraction result is inferred from finite freeness alone without this coefficient argument.

For step 5 I read `lem-sbc-regular-principal-prime-localization-dvr` in the DAG and its public upstream Lean statement and proof. It needs only a Noetherian ring, an injective multiplication map for the generator, and a prime principal ideal. Steps 1–2 prove those hypotheses twice. I also opened the definition nodes for localization at a prime and a DVR: the former supplies the maximal ideal pR_p, and the latter defines uniformizers as its generators. Thus the chosen t_i and x_i are the uniformizers asserted here. Domain fraction multiplication proves injection of the localization maps.

For step 6 I opened `lem-weil-pbc-localization-base-change`; its statement identifies the tensor product with localization at the image of the coefficient multiplicative set, exactly the set S in use. Finiteness after base change is not left as an unexplained theorem: the localized monomial basis is obtained by expanding the numerator and clearing the finitely many coefficient denominators. Independence follows from the original basis. The nonzero-denominator domain test is explicit.

Step 7 is an elementary fraction calculation, with both directions of the quotient-localization map displayed. The quotient B/(x_i) is a domain by step 2, and no denominator dies by step 4. Images of R minus (t_i) are all nonzero elements of R/(t_i), so the scalar localization is its fraction field. The earlier basis localizes coefficient by coefficient. This distinguishes (x_i) from (t_i)=(x_i^n), which would be a false identification if n>1. No general localization-quotient node with narrower hypotheses is cited for this calculation.

For step 8 I opened `lem-weil-pbc-finite-dimensional-domain-is-field`; its exact hypotheses were obtained in step 7, giving the field D. I opened `lem-weil-pbc-finite-algebra-is-integral` and `lem-weil-pbc-integral-maximal-contracts-maximal`; they give respectively integrality of C over V_i and contraction of every maximal ideal to the unique maximal ideal of V_i. Then t_i=x_i^n belongs to every maximal ideal, whence x_i does. The field quotient makes (x_i) itself maximal and proves uniqueness, so this step does not assume the sought localness or claim that arbitrary finite localizations remain finite.

For step 9 I opened `lem-weil-pbc-local-ring-unit-criterion`, which says that elements outside the unique maximal ideal are units. The kernel of B to D is (x_i) by the domain fraction test, so it applies to every required denominator. The two actual maps between C and B_(x_i) are written and their composites checked on coefficients and fractions. This proves the canonical V_i-algebra identification and then finiteness, rather than assuming the original finite map remains finite after localizing at an arbitrary prime above it. Step 10 checks both fraction-field identifications directly by a common-denominator formula and computes the ideal-power equality using x_i^n=t_i.

For step 11 I opened `lem-sc-dvr-dimension-one` and `lem-weil-pbc-primes-of-localization`. Their statements respectively give dimension one of A_i and an inclusion-preserving bijection of its primes with the primes of B contained in q_i. A hypothetical prime strictly between 0 and q_i would yield a chain of length two in A_i. Conversely the finite product equation for f and primality of any height-one boundary prime put some nonzero q_j inside it, forcing equality by height one. This uses the statement of the cited localization node, not its proof or a generic definition of dimension.

I checked delivery-errors B–E against the written JSON: there are no new statement-only obligations, duplicates, hollow objects, or clause-restatement helper nodes; all non-elementary tools are cited by their statements; no source reference substitutes for a DAG citation; no normality, n-invertibility, or finiteness of arbitrary prime localizations is silently used. Every step is below 2000 characters (largest 826), and the elementary steps are actual generator/fraction/ideal computations from earlier steps. `citations.json` was verified against the exact statement strings read from the DAG.

Small cases checked: if r=0 there are no indexed assertions and f=1 is in no prime, including d=0; if r=1 the boundary quotient has empty monomial basis product {1}; if n=1 the presentation is B=R with the expected identical localizations. In residue characteristic dividing n, the closed fiber over (t_i) can have nilpotents, and the proof only uses the quotient by x_i, never claims the entire fiber is reduced. No extra tame or separability assumption enters. The nonzero quotient domains exclude a killed parameter, zero denominator, or zero ring in every indexed case.

## Unfinished work

None in the mathematical split. The required dry run and delivery results are recorded below when available.
