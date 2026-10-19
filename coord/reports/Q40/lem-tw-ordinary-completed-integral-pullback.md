1. Files written

- `dag/nodes/sec-purity-real-sheaves/lem-tw-ordinary-completed-integral-pullback.json`: statement node, now split in seven steps, unchanged statement, no Mathlib match.
- No new nodes or Mathlib leaves.
- `citations.json`: nineteen exact statement quotations for the nineteen step/node citations.

2. Attachments

None. Searched `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` by exact blueprint tag, ordinary/completed integral pullback names, and completed/pullback concept phrases. The only completed-pullback discussion initially returned was the integral exceptional inverse-image docstring in `SixFunctors/Etale/Derived/IntegralCoefficients.lean:316`; it does not give this theorem. The upstream master was also searched as reference, not accepted as finished proof. No exact declaration was found.

3. WANTED

None. All source documents used are present.

4. What was wrong or incomplete

The item's proof was empty. Its source already flags the explicit quotient-cone normalization as an agent formulation; Remark 6.8.15 is not by itself a proof of that map's invertibility. I supplied the ordinary-pullback local-model argument and a strict isomorphism between its reduction tower and the prescribed finite-pullback tower. This proves the assertion for the actual map, including transition maps and naturality. The statement, coefficient category, hypotheses, inherited searches and blueprint ancestry were retained. There is no statement dispute.

The integral-category comparison is not inferred from a similar name: the existing `lem-weil-pbc-integral-stratified-perfect-characterization` explicitly identifies the category in this item with its three equivalent descriptions, including intrinsic completeness and compatible origins. Neither the condensed coefficient category nor a discrete non-torsion etale category is substituted. I do not use the overstrong-looking arbitrary-morphism coefficient-isomorphism assertion in `lem-weil-pbc-profinite-coefficient-inverse-image`; only the immersion restriction result is used for strata, and the arbitrary-morphism coefficient map is retained as a map.

5. Unfinished work

None for this one-level split. Existing unsplit dependencies remain existing DAG items; this delivery does not split or edit them.

## Not duplicates

No new nodes. Whole-DAG and whole-blueprint searches for `stratified perfect`, `completed pullback`, `ordinary pullback`, and `completion unit` led to reuse of the integral characterization, ordinary ringed pullback/composition and canonical Koszul/quotient reconstruction nodes. In particular the proper-base-change preservation proposition is not substituted: it concerns completed pullbacks in a proper square and does not prove this ordinary-pullback comparison.

## Mathlib searches

Ran the prescribed command through `/home/ubuntu/weil-launcher-nt/msearch.py`, recording its actual queries in `searches.jsonl` and appending their outcomes to the item's inherited searches. Two LeanFinder phrasings returned underived sheaf pullback, affine-limit lemmas and period rings. LeanSearch returned ordinary module adic-completion bijectivity lemmas. Grep returned the continuous coefficient sheaf/cohomology definitions and unrelated preradical colon code. The initial Loogle pattern with `IsIso` reported an unknown identifier, so it is recorded as unavailable, and the corrected `SheafOfModules.pullback` search returned ordinary sheaf pullback and its composition. Read the returned types, `Mathlib/AlgebraicGeometry/Sites/ElladicCohomology.lean:45-85`, `Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackContinuous.lean:85-130`, and `Mathlib/RingTheory/AdicCompletion/Basic.lean:640-658`. These do not state the derived constructible adic theorem or specialize to it in one line. No new search result is represented as a Mathlib leaf.

## Review by Q40

I read Bhatt--Scholze, Proposition 6.6.11 (both directions and its definition of perfect local values), Lemma 6.5.9(4),(5), and Remark 6.8.15 in the local PDF. The first is the local-model route, while the remark identifies ordinary ringed operations with the constructible operations. I read the current `lem-tw-dual-negation` proof and its unit/chapter: this comparison supplies the ordinary realization of the fibre used by its first sentence and does not replace a linear-algebra step in the unit. No unit record is changed and no new node needs a separate source review.

For step 1 I opened the integral stratified-perfect characterization and checked the exact final sentence naming `def-weil-derived-complete-integral-detailed`. Its assumptions match both schemes: a finite noetherian affine cover follows from locally noetherian plus quasi-compact, and finite dimension and ell-invertibility are explicitly assumed. This retains uniform boundedness of the reductions, rather than merely levelwise constructibility.

For step 2 I opened the stratification definition and the pro-etale inverse-image functoriality theorem. Its first clause really does say base change sends covers to covers. The affine quotient identity in the step proves the locally closed base-change assertion instead of leaving an uncited immersion-stability theorem. Noetherianity makes the locally closed images constructible. Empty inverse-image strata are removed. This is elementary scheme geometry together with the cited covering assertion.

For step 3 I opened the ordinary ringed derived monoidal-comparison theorem: its statement explicitly gives arbitrary ringed-topos pullback composition without flatness or boundedness hypotheses. I also opened the immersion comparison, whose ordinary restriction functor is exact, and the ringed slice-localization theorem, whose second displayed comparison is exactly the cover restriction needed. I checked the composite coefficient maps on each finite projection. The bounded finite-projective model calculation takes a finite free vector to that same vector and passes to idempotent summands; it does not assume the arbitrary completed coefficient structure map is an isomorphism. Sources read: Stacks `sites-cohomology.tex`, Tags 0D6D (`lemma-derived-pullback-composition`) and 07A4 (`lemma-pullback-tensor-product`), as well as the local-model passage of Bhatt--Scholze.

For step 4 I reread the reverse implication in the integral characterization and the actual definition of the bounded complete category. The latter requires intrinsic Koszul-unit completeness, which is stronger and more precise than an arbitrary isomorphism to the endpoints of a triangle. This is why it suffices for the normalized map in this item. Uniform bounds and compatible origins come from that existing characterization, not from an unstated descent argument.

For step 5 I opened the derived-pullback theorem, K-flat pullback theorem, finite-constant exactness theorem and exact monoidal inverse-image theorem. The first two explicitly say the chosen flat-term K-flat pullback computes the derived functor and stays in that resolving class. The third identifies the finite constant ring structure map and gives exact finite pullback. The fourth supplies exactness and tensor preservation; relative tensor follows by its balanced cokernel presentation. I checked the maps and inverse on balanced sections, including the coefficient action through each projection, the actual transition maps, and compatibility with each quotient arrow. The source K-flat statement is Stacks Tag 0G7E (`lemma-pullback-K-flat`), read in `sites-cohomology.tex`; no flatness of `f^{-1}B_Y -> B_X` is used.

For step 6 I opened both coefficient lemmas and the full Koszul reconstruction statement. The former give a domain/PID and finite quotients, and the displayed two-term resolution checks the perfect-quotient hypothesis for every positive n. I read Stacks Tag 099M (`proetale.tex`, `lemma-naive-completion`), Tag 0A0E (`algebraization.tex`, `lemma-derived-completion-koszul`), and the coefficient flatness/quotient statement Tag 093M (`sites-modules.tex`, `lemma-completion-flat`). The reconstruction node explicitly identifies its isomorphism with the canonical quotient unit, rather than only its target object. I opened the integral operation definition and its well-definedness theorem and checked that their limit is exactly the strict product-cone model used here. Applying the strict tower isomorphism acts on both coordinates and preserves the zero coordinate; this gives equality with the specified eta, not an inference of equality from finite projections alone.

For step 7 the generator formula makes the comparison commute with every map between resolutions at the chain level. The two cited descent statements really provide the canonical resolving-class comparisons and preservation of quasi-isomorphisms. Thus the square survives localization and inverted comparison maps. This proves naturality and independence under the designated comparisons; no arbitrary functorial choice of cones is introduced.

I checked delivery-errors B--E against the final files: self-contained unchanged statement; no new nodes, duplication or relabelled clauses; all used non-elementary facts have existing cited statements; no proof of a cited node is substituted for its statement; nineteen verbatim quotations cover every use. All seven steps are below 2000 characters. The new proof does not alter definitions or target hypotheses and does not cite SGA. Edge cases checked: empty X or Y, zero complex, identity f, a closed stratum and its open complement, empty pulled-back strata, finite projective summands rather than only free models, torsion perfect model `[R --t^n--> R]`, and arbitrary non-base-linear f. The quotient formulas also work for n=1 and all successive quotients. No additional hypotheses are needed. Generic ringed, adic-characterization, coefficient and completion tools outside the linear-algebra unit are listed in `split_report.tool_uses` with their role.
