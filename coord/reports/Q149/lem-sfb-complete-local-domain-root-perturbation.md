# Stage-1 report: lem-sfb-complete-local-domain-root-perturbation

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-complete-local-domain-root-perturbation.json`: existing statement, now split into six steps. Statement and statement dependencies unchanged. Mathlib verdict: no exact or one-line match.
- `citations.json`: verbatim statements for all seven citations, indexed by proof step.
- `searches.jsonl`: actual msearch results, including the repeated item search with a different phrasing and searches for the denominator input.
- `report.md`: this report.

No new nodes; no new Mathlib leaves. All mathematical arguments remain in the item's proof steps.

## Attachments

No attachment for the item: searches of `lean/WeilConjectures/` by its blueprint tag and by root perturbation/Krasner terminology found no declaration stating it.

The already attached declaration `IsLocalRing.bijective_away_lift_fractionRing_of_ringKrullDim_eq_one` belongs to existing node `lem-sc-local-domain-dim-one-principal-localization-fraction-field`, `lean/WeilConjectures/RingTheory/LocalDomainDimOnePrincipalLocalization.lean:47`. I read the signature and its full proof; it has no sorry and supplies exactly the canonical fraction-field comparison used in Step 1. This is reuse of an existing node, not an attachment claim for the item.

## WANTED

None. The proof is from the locally available Stacks text.

## Audit findings and corrections

I read `literature/stacks-project/more-algebra.tex`, Tag 09EI, label `lemma-krasner`, statement and complete proof (lines 33748–33810), and the invocation in Tag 09EJ immediately afterwards. The item's parameter-ideal precision is exactly the precision maintained by that proof, even though the displayed Stacks statement uses maximal-ideal powers. The item's explicit Noetherianity remains unchanged. No invertible derivative, monicity, fixed degree, valuation or normality assumption was added.

The source labels its iterates starting at the denominator exponent m while also claiming that all increments preserve precision pi^c. I avoid relying on that indexing: start the iteration at C=max(c,M+1). This makes both the quadratic error estimate 2k>=M+k+1 and preservation of t^c immediate. The new proof spells out the base case, correction, induction step and limit. This is an indexing clarification of the same Newton construction, not a statement dispute or route replacement.

The last step of the source says that taking a limit finishes. Here precision in the possibly non-maximal principal ideal t^c is proved by dividing x_k-a by t^c before forming a compatible family modulo maximal-ideal powers. Thus no unstated theorem about closed ideals, completeness for a different ideal, or continuity of polynomial evaluation is used. Polynomial evaluation modulo each ideal is justified by the displayed monomial difference formula.

The imported nearest blueprint ancestor is null. I read `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/_section.md` and its direct-image detailed proof, especially (3). It no longer states the long historical algebraic reduction. I retain the full existing historical provenance and via chain and say explicitly that this algebra lemma is absent from the latest detailed proof. Whole-blueprint searches for root perturbation, Krasner, complete local, principal localization and maximal ideal radical found no blueprint restatement that could replace this item or its denominator input. The arbitrary-rank henselian Krasner node `lem-per-henselian-krasner-neighbourhood` concerns conjugate separation and field containment, not coefficient perturbations or roots in a complete local domain.

The denominator theorem is a generic off-unit algebra tool. It does not replace any unit step; `split_report.tool_uses` records its role. The remainder of the proof follows Stacks 09EI. The source tags 00CM/00C8 on that existing theorem are inherited coarse localization references; I relied on its actual statement and read its complete project proof, not on an inferred property of those tags.

## Mathlib and duplicate searches

I preserved all inherited searches, citations and provenance in the item, and ran the required msearch services for the item plus a second semantic phrasing. The actual results are in searches.jsonl. HenselianLocalRing.is_henselian requires monicity and a unit derivative. The p-adic hensels_lemma has a norm and Z_p base. The normed-field continuity-of-roots theorem has monicity, equal degree and splitting hypotheses. IsAdicComplete.henselianRing gives the henselian property, not this nonunit-derivative perturbation theorem by one-line specialization. The denominator search found Mathlib's `ringKrullDim_eq_one_iff_of_isLocalRing_isDomain` (LocalRing.lean:20), which is already used by the existing localization node; it is supporting algebra rather than a match for the item.

## Not duplicates

No new nodes. Reused `lem-sc-local-domain-dim-one-principal-localization-fraction-field` after searching the whole DAG for dimension-one localizations, radicals and principal ideals, and reading its statement. In particular I did not create a second dimension-one power-divisibility lemma.

## Review by Q149

I read Tag 09EI itself rather than infer the argument from the parent item or from its citations. There are no new nodes requiring further source review. I opened every dependency's JSON statement and copied it verbatim into citations.json. I checked the return cases B–E against the actual proof as follows.

Step 1 uses the exact isomorphism stated by `lem-sc-local-domain-dim-one-principal-localization-fraction-field`, with B=R and f=t; locality, dimension one, domain and t nonzero in the maximal ideal are all item hypotheses. `def-weil-ring-localization-away` explicitly represents every element as u/t^M. Applied to the preimage of d^{-1}, that yields du=t^M using injectivity into the fraction field. This reads only the node's conclusion, not an intermediate fact from its proof. The chosen n=M+C is positive and independent of Q.

Step 2 uses only the finite-sum definition from `def-weil-polynomial-ring`; the binomial and monomial-difference calculations are written out. In particular the high-degree terms of Q are still divisible by t^n, so the argument does not need a degree bound. Step 3 introduces a single explicit recursion with its base case and invariants. Existence and uniqueness of e_k follow from the stated divisibility and domain cancellation. The correction is in R even when d is a nonunit.

Step 4 reuses the Step 2 finite-sum calculation, with `def-weil-polynomial-ring` cited. I checked each ideal exponent separately: C+k, 2k and n+k are all at least M+k+1. The term involving P'(x_k)-P'(a) is accounted for; it is not replaced by an unsupported equality. Every increment has exponent k>=C, preserving the initial precision.

Step 5 cites `def-weil-pbc-adically-complete-ring`, whose statement supplies the bijection to compatible residue families. The divided iterates y_k have differences in t^(k-c), hence in m^r eventually, since t is in m; telescoping verifies compatibility. Completeness is used for the original maximal ideal only. The resulting b=a+t^c y proves membership in the required principal ideal directly. Step 6 cites the finite-sum polynomial definition for reduction modulo m^r and the same completeness node for its explicitly stated separatedness intersection. These are direct consequences of the definitions, not invocations of uncited analytic convergence theorems.

Small cases: for c=0 we still take C>=M+1, so all indices and cancellation steps are meaningful. For a unit derivative one may take M=0; then n=C>=1 and the error exponents still work. For Q=0 the unique e_C and all corrections are zero, so b=a. Linear P with a nonunit derivative gives b=a-Q(a)/d in the constant-perturbation case, and the imposed divisibility ensures this lies in R. Over a singular one-dimensional complete domain such as k[[s^2,s^3]] with t=s^2 and d=s^3, du=t^3 with u=s^3 verifies that no DVR or normality assumption entered. Positive characteristic is allowed: binomial coefficients are integral, with no division by factorials. The hypothesis d!=0 excludes constant P and inseparable multiple-root failures; the zero ring and fields are excluded by the domain/dimension/t hypotheses. There is no assertion of uniqueness of the perturbed root.

No step exceeds 2000 characters. Every new subclaim is either an explicit finite algebra computation, the displayed induction, or the direct inverse-limit definition. No clause of the item was hidden in a newly named node. All citation quotes are actual complete statements and all proof dependencies are exactly the union of step uses. No target, Lean file, repository file or launcher file was changed; no compiler was run. I also read Stacks Tag 0317, algebra.tex label definition-complete, which states both the inverse-limit isomorphism and the intersection-zero condition used in Steps 5–6.

## Unfinished work

None in the requested stage-1 split. Independent maintainer review remains part of the delivery process.
