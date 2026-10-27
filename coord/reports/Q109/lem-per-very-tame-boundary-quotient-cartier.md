## Worker report

Item: lem-per-very-tame-boundary-quotient-cartier. Group Q109. Stage 1 only, 2026-10-24.

Files written:

- dag/nodes/sec-deligne-laumon-a1/lem-per-very-tame-boundary-quotient-cartier.json: split into eight proof steps; no Mathlib match.
- dag/nodes/sec-deligne-laumon-a1/lem-per-weil-divisor-strict-local-cartier-test.json: new statement-only general Cartier test; unsplit, no Mathlib match.
- citations.json: one verbatim statement quotation for every cited node in every numbered step.

## New nodes

lem-per-weil-divisor-strict-local-cartier-test is the only new node. It is a general assertion for a fixed Weil divisor on an arbitrary Noetherian normal scheme, with no group, boundary, or modification. It isolates faithful-flat testing of the rank-one reflexive module of a divisor, not a clause of the item. The intended proof identifies the divisor module with its strict-local scalar extension (using the normal, codimension-one reflexive description and flat base change of finite presentations), descends rank-one freeness through the flat local map, and uses the height-one valuation intersection to identify the resulting Cartier equation. Local generators spread on pointed etale neighborhoods. This argument is report material only: the node carries a statement, no proof or proof dependencies. Its negative-coefficient formulation is useful and does not assert effectivity in that case.

## Attachments

None. I searched the live project under lean/WeilConjectures for the exact blueprint tag and for very-tame, invariant-boundary, eigenparameter, quotient-Cartier and strict-local-Cartier terms. No declaration states this item or the new local test. The existing sorry-containing and partial geometry interfaces do not qualify as attachments. Mathlib's AlgebraicCycle.IsWeilDivisor and weilDivisors are definitions of cycles, not the Cartier test.

## WANTED

None. All sources used are present locally. No SGA source was used.

## Source and blueprint

I read ILO VIII 5.3.5, 5.3.8 and 5.4.1, printed pp.124–126, and VI Proposition 3.5(a), proof 3.7(a) and the opening of 3.7(b), printed pp.74–75. VIII 5.3.8 constructs an invariant power of an equivariant boundary equation and then pulls the Cartier divisor back to the regular modification. VI 3.5(a) supplies the eigenchart without needing generic freeness or integral X globally. The item is an extracted lemma from that paragraph, not the full modification theorem; I kept its weaker hypotheses and all conclusions. In particular I did not import the full modification theorem as a dependency, since it cites the item.

I read the current latest blueprint chapter, unit sk-p-dl-a1-perverse, and lem-per-artin-gabber-affine-curve.proof.md. The current ancestor Step 3 is the duality/cosupport step. The inherited chain realizes the regular-pair/purity input needed below that step. The split retains this route and makes precise the VIII 5.3.8 subargument at the existing blueprint.from.place; it does not change any unit or chapter. No blueprint_update field is removed or overwritten.

The item's original citation of def-trf-fs-log-blowup for “very tame” was insufficient: that node defines fs log structures and log blowups, not actions. I added def-per-very-tame-divisorial-action to that sentence and stmt_deps, retaining the fs citation for the log structure. This is a definition-reference correction, with no mathematical statement change or disputed hypothesis.

The original item was unsplit. A central distinction is that merely obtaining Cartier support does not imply the *reduced* Weil divisor is Q-Cartier without a coefficient argument. Step 5 supplies that argument: at each selected branch t_i choose the local ramification integer e_i, use f=product t_i^(e_i), and descend f^N. This has coefficient N at every image branch. Raising it to |G|/N supplies the same global multiple |G|E at every strict localization. This works even for a nonfaithful action; no false assumption that all ramification indices coincide or that the action is generically free was added.

## Searches

All Mathlib searches were run through the required batch2/msearch.py Q109 lem-per-very-tame-boundary-quotient-cartier command, and searches.jsonl is the unmodified log. The item retains its previous recorded searches and adds this run's actual searches. The new node has LeanFinder, LeanSearch, Loogle and grep records copied from the corresponding actual log entries. Both natural-language phrasings were read. No unavailable service was called a negative result; all services used here returned results.

The ramification searches were exploratory: Mathlib/NumberTheory/RamificationInertia/Valuation.lean lines 34–61 gives intValuation_liesOver and valuation_liesOver for globally Dedekind domains. It does not by itself supply height preservation for arbitrary normal rings, or the geometric strict-local test. Rather than create a composite new node for a few-line application, I reused the existing going-down, incomparability, lying-over and normal-domain DVR nodes and wrote the prime-chain and uniformizer arguments in the item.

Before creating the new node I searched the entire DAG statements, titles and ids for Weil divisor, Q-Cartier, invariant subring, normal quotient, Cartier descent, strict-local Cartier and rank-one reflexive tests. I searched the tags 0EBM, 0AY6, 0BE8, 00O1 and 025P and opened the resulting candidates. tools/blueprint_refs.py search was run for Cartier, invariant, valuation, height one, strict local Cartier, Weil divisor, normal domain, strict henselization and ramification. No imported blueprint node states the new test. The useful generic normality, prime comparison and boundary-factorization nodes are cited instead of duplicated.

## Not duplicates

lem-per-weil-divisor-strict-local-cartier-test vs lem-trf-normal-domain-principal-divisor-kernel: the existing node describes normalized valuations and the kernel of a principal-divisor map in one normal affine domain; it does not descend Cartierness of a fixed Weil divisor from strict localizations.
lem-per-weil-divisor-strict-local-cartier-test vs lem-sfb-stalk-nonzerodivisor-cartier-spreading: the existing node assumes a given closed ideal already principal at ordinary stalks; it neither constructs the divisorial ideal of a Weil divisor nor tests its freeness after strict henselization.
lem-per-weil-divisor-strict-local-cartier-test vs lem-trf-etale-reduced-cartier-descent: the existing node concerns Cartierness of a fixed reduced closed subscheme; a multiple aE is generally nonreduced and needs a Weil-divisor Cartier test.
lem-per-weil-divisor-strict-local-cartier-test vs lem-sfb-normal-group-vertical-cartier-descent: that statement concerns a vertical Cartier divisor on a smooth group scheme and descent along its identity section; it assumes Cartierness and has no strict-local Weil test.
lem-per-weil-divisor-strict-local-cartier-test vs lem-weil-pbc-finite-projective-descends-flat-local: that is module freeness descent for a supplied finite module, not the identification of a divisor module under strict localization.

lem-per-weil-divisor-strict-local-cartier-test vs lem-weil-pbc-flat-under-regular: the existing node descends regularity along a flat local ring map; it does not identify divisorial modules under strict localization or test Cartierness of Weil divisors on possibly singular normal schemes.
lem-per-weil-divisor-strict-local-cartier-test vs lem-sc-function-field-sections-glue: the existing node glues a rational function already regular at every ordinary local ring; it neither tests Cartierness after a residue-field extension nor constructs an equation for a fixed multiple of a Weil divisor.
lem-per-weil-divisor-strict-local-cartier-test vs lem-pc-regular-curve-divisor-calculus: the existing node assumes an integral regular scheme of dimension one, where every Weil divisor is Cartier; the new test allows normal singular schemes of arbitrary dimension and tests a fixed multiple on strict local rings.

## Review by Q109

I checked delivery-errors B–E with the node files and source passages open. The new node introduces Y, E, all coefficients, codimension-one subvarieties, the meaning of Cartier/effective, strict local rings, normalized valuations and the fixed positive integer a. It does not use a tag as the definition of a notion. I read Stacks divisors.tex 0EBM (lemma-normal-class-group), 0AY6 (lemma-reflexive-over-normal), 0BE8 (lemma-normal-c1-injective, including its normal-domain intersection proof), algebra.tex 00O1 (lemma-finite-projective-descends), and the normality input 025P. The local-test statement is expressly an agent-formulated consequence, not falsely attributed verbatim to any one tag. Its proof belongs to its later split, not its statement. Its geometric pullback keeps the original coefficient at each etale branch; it does not require irreducibility of the strict-local pullback of a prime divisor.

Step 1: I opened finite-quotient-strict-local-invariants and regular-boundary-divisorial-chart. The former really states R=A^H, finite A/R and Noetherian Y; the latter gives the fs N^r chart and parameter representatives on a regular Noetherian SNC pair. Strict-henselization-regular, regular-local-localization and regular-ring-normal supply exactly regular A, its regular prime localizations and normality. Faithful-flat strict henselization and per-faithfully-flat-normal-ring-descent descend normality to ordinary local rings. The intervening fixed-fraction argument is written out, not attributed to the quotient definition. No source hypothesis of generic freeness is silently used.

Step 2: I read the statement of very-tame-equivariant-sharp-chart: it gives characters in H-fixed mu_N, not merely tangent-space eigenvectors. The action is trivial on the characteristic by the cited divisorial very-tame definition, and N is invertible. Changing a sharp chart multiplies generators by units, so the regular-parameter property from Step 1 is retained. The UFD-boundary-factorization node states exactly the localization-unit classification; reducedness removes repeated exponents. The selected subset S gives b and its actual character. This is not a new node restating the eigenvector clause.

Step 3: I opened finite-algebra-is-integral, integral-incomparability, going-down-normal-integral and injective-lying-over: the required inclusions are injective, integral and between domains with normal base. The two explicit prime-chain lifts/contractions give equal heights and primes over every height-one prime. I corrected the draft to cite rem-pc-regular-normal and explicitly restrict to open-and-closed integral components on affine charts; source affine rings need not be domains globally. The generic admissible-quotient-affine-integral-charts statement really supplies the invariant affine chart identification and orbit fibres. The new node is cited for the definition/compatibility of E_R, rather than relying on its future proof.

Step 4: the only cited theorem is injective-lying-over, whose statement supplies the prime P used. The nonzerodivisor and support arguments are elementary ring arguments written explicitly; the power need not define the reduced divisor as a scheme. I did not identify its coefficients with those of E at this step.

Step 5: I read the entire normal-domain-principal-divisor-kernel statement: it gives DVRs at height one and agreement of normalized orders with Weil coefficients. UFD-boundary-factorization gives prime t_i and absence of other prime factors. No ramification theorem is hidden: writing z=u*pi_i^m and mapping a unit through the local DVR map proves the needed valuation formula in two lines. The choice of e_i>0 is justified by contraction of (t_i) and locality. Distinct branches over one downstairs prime give N after division by their own e_i. This repairs the otherwise unjustified passage from Cartier support to Q-Cartier coefficients.

Step 6: I checked all hypotheses of the new test: Y is normal and Noetherian by Step 1, E is finite effective codimension one by Step 3, and M=|G| is a single positive integer. The coset partition gives M/N integral even with ineffective inertia. The test gives effective C with Weil divisor ME and the demanded etale-local equations; it does not assert that C itself is reduced.

Step 7: the pulled-back equation remains nonzero at generic points under birationality and hence in the regular local domains upstairs. Thus the whole pullback is an effective Cartier divisor. I kept the inverse-image support and the reduced induced closed subscheme separate; mere set inclusion is not used as a factorization of a nonreduced closed immersion.

Step 8: I added an explicit citation of etale-stalk-invariants for regularity on the normal-crossings etale chart. I read its statement: it really compares the ordinary local rings at the specified etale points, with no finite-type-over-a-field assumption. The UFD node then applies. The containment V(c') in V(T) gives T^a in (c'), so the localization-unit hypothesis is verified rather than assumed. Radical factorization yields a subproduct of distinct parameters, hence a pure codimension-one union of ambient components, not an arbitrary closed subset of the boundary. For strictness, the strict-boundary definition gives exactly regularity and codimension of the selected component intersections. No stronger neighborhood version of the nc-subboundary-branch-atlas node was applied to weaker input.

Small cases: B empty gives S empty, b=f=c=1 and E=C=0, including a zero-dimensional or empty scheme. Trivial G gives N=M=1 and recovers the original reduced Cartier boundary. For k[[t]] with t mapped to zeta*t, R=k[[t^N]], the unweighted b^N already has downstairs multiplicity one, while the weighted f^N has multiplicity N as required; this checks that the proof never mistakes b^N for N times the reduced image. For k[[x,y]] with simultaneous sign action, B=(x), the quotient image is not Cartier but twice it is, matching the source's orbifold warning. Multiple branches over one prime and nonfaithful H were checked using the branchwise e_i calculation. For the new test, a=1, negative coefficients, E=0, a non-Cartier divisor on the quadric cone and a split etale prime divisor all give the expected conclusions. The NC conclusion permits nonstrict global self-intersections; strictness is concluded only under the ambient strict hypothesis.

All cited-node statements are copied verbatim in citations.json; I verified their hypotheses in the numbered paragraphs above. Every step is below 2000 characters. I created no elementary-only, duplicate or clause-restatement node. No parent modification theorem is cited, so the proof does not create the obvious cycle. Off-unit inputs are declared only as split_report.tool_uses with their generic algebra purpose; I did not write maintainer tool_uses fields. There are no Lean edits or compiler invocations.

## Unfinished work

The new local Cartier test is intentionally statement-only and remains an unsplit stage-1 item. Nothing else was left unfinished in this one-level split. Final delivery checks are recorded by deliver.py below.
