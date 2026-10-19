## Worker report

Files written: `dag/nodes/sec-proper-base-change/lem-weil-pbc-minimal-prime-finite-type-algebra-finite-away.json` (statement, split; no exact Mathlib match). No new nodes and no new Mathlib leaves. `citations.json` quotes each cited statement verbatim. The three uncommitted duplicate proposals from the earlier sandbox attempt were removed.

Attachments: none. Searches under `WeilConjectures/` for the exact blueprint id and for generic finiteness, finite spectrum and minimal-prime localization found no project declaration stating the whole item. Upstream master's sorry declarations are not attachments.

WANTED: none.

The item's statement agrees with Algebra Tag 02ML, `lemma-generically-finite`, and was not changed. The previous attempt's 00I2/00I6/00J1/02MI tags were incorrect: the actual cited labels map to 0ALW/00EU/0544/0H8X. Its claim that coefficient denominator clearing already gives membership in pS_g1 was unjustified; membership is needed and used only in S_p. Its finite-spectrum child excluded the zero ring, while the item allows empty fibres. Its statement dependencies incorrectly included proof lemmas. These faults are repaired.

The old search log contained unrelated historical queries, while all three proposed nodes recorded the same unrelated queries; this was not evidence of a search-tool malfunction. I ran the prescribed msearch command anew for the item (two semantic phrasings, Loogle, grep, and unavailable LeanSearch), recorded the actual queries and responses, and read the returned quasi-finiteness/localization signatures. Localization.exists_finite_awayMapₐ_of_surjective_awayMapₐ requires an integral intermediate algebra and a surjective localized map, absent here; localization preservation assumes finiteness already. No hit states this item or specializes in one line to it. No new-node searches are now required because no new node remains.

The chapter and unit records were read; this algebra lemma belongs to the inherited generic-finite shrinking branch of the classical constructibility input. I keep the 02ML source route. The only off-unit statement that is not a Mathlib leaf is the existing general finite-spectrum algebra theorem; it is used as a generic algebra tool: the unit has no separate finite-spectrum theorem. The maintainer may record the cross-unit use; this delivery does not write `tool_uses`. No unit or chapter file was changed.

Nothing remains unfinished before the second reader, subject to the dry run below.

## Not duplicates

The proposed finite-type-finite-spectrum-finite-dimensional node is subsumed by `pqf-lem-finite-type-algebra-finite-spectrum`, whose statement also includes the zero ring. The proposed minimal-prime-localization-locally-nilpotent node is the first clause of `lem-weil-pbc-minimal-prime-reduced-localization-field`. The proposed locally-nilpotent-base-change node is exactly `lem-weil-pbc-locally-nilpotent-extension`. All three proposals were dropped, rather than delivered. Searches of the whole DAG by the actual Stacks tags and labels found these existing statements; blueprint_refs searches for 0ALW, 00EU, 0544, 02ML, finite spectrum, minimal prime and locally nilpotent found no blueprint equivalent requiring another reference.

## Review by NK

I read Algebra 02ML (`lemma-generically-finite`) and its source lemmas 0H8X (`lemma-quasi-finite-above-p`), 0ALW (`lemma-finite-type-algebra-finite-nr-primes`), 00EU (`lemma-minimal-prime-reduced-ring`) and 0544 (`lemma-locally-nilpotent`). I checked the tags against tags/tags, rather than trusting the earlier record. The source assumes only finite type, minimality, and finitely many primes lying over p; it does not assume R noetherian or reduced, nor a nonempty fibre. The item retains exactly those hypotheses.

Step 1 takes the prime bijection from lem-weil-pbc-fibre-ring-primes-bijection, whose full statement gives precisely contraction equal to p, and finite-dimensionality from pqf-lem-finite-type-algebra-finite-spectrum, which explicitly allows zero. Polynomial expansion of pure tensors shows that base change retains the generators. Step 2 takes the compatible quotient identification from lem-weil-pbc-fibre-ring-localization-quotient, and the residue quotient and fractions from def-weil-pbc-localization-at-prime. Linear dependence of powers over a field gives monic relations; for a nonzero fibre a relation cannot have only a nonzero constant term, and for a zero fibre X is used. The coefficients are lifted in R_p before any smaller localization is chosen.

Step 3 uses exactly the first clause of lem-weil-pbc-minimal-prime-reduced-localization-field, so its optional reducedness hypothesis is not used. The statement of lem-weil-pbc-locally-nilpotent-extension applies to the ring map R_p to S_p and the ideal pR_p; this extended ideal is pS_p. These two statements give nilpotence of each evaluated relation, without any uniform nilpotence exponent for the whole ideal.

Step 4 uses the fraction equality definitions in def-weil-pbc-localization-at-prime and def-weil-ring-localization-away. I wrote the actual product-of-denominators formula and the annihilator u_i for each relation. Step 5 uses the away-localization fraction definition again: every factor of g is invertible after inverting g, so those annihilators kill the relations and then can be cancelled. No injectivity of R_g1 to R_p, or S_g1 to S_p, is assumed. Step 6 uses that same fraction definition and an explicit exponent-decreasing substitution for each monic equation. The bounded monomials form a finite spanning set; no uncited integrality-to-finiteness theorem is being used.

I checked B through E against the actual node files: no new or duplicate nodes survive; every non-elementary input is a cited statement, every citation has its verbatim quote in citations.json, proof dependencies are exactly the uses union, and the statement dependency is only the away-localization notion already named by the item. No definition is cited as a substitute for an unprovided theorem. The six proof steps carry the 02ML argument themselves.

Small cases checked: R a field with p=0 reduces to finite-spectrum finite-dimensionality; S=0 gives the zero fibre and monic relation X; R=k[epsilon]/(epsilon^2), p=(epsilon), checks that nonreduced bases require the nilpotence power; an empty generating list gives the single spanning monomial 1; infinitely many nilpotents in the base do not require a uniform exponent because there are finitely many relations. Thus the earlier zero-fibre omission and the premature ideal membership are actually resolved. This is the worker's self-review; a fresh second reader must still review and deliver.

## Second reading by NK

- Item statement: checked against Algebra Tag 02ML (`lemma-generically-finite`) in `literature/stacks-project/algebra.tex`; finite type, minimal-prime, finite-fibre-prime, and empty/zero-fibre cases all match.
- Step 1: checked the cited fibre-prime bijection and finite-spectrum algebra statements; their hypotheses and conclusions supply exactly the finite-dimensional fibre argument, including the zero ring.
- Step 2: checked the cited fibre/localization quotient and prime-localization definitions; the monic relation construction and coefficient lifting are valid, with the zero fibre handled by (X).
- Step 3: checked both cited nilpotence statements; minimality alone gives local nilpotence and extension gives each evaluated relation a (possibly separate) exponent.
- Step 4: checked the cited fraction definitions; denominator products and the localization equality criterion justify the individual annihilators without an injectivity assumption.
- Step 5: checked the away-localization fraction definition; after inverting the product, each annihilator factor is cancellable and the monic equations persist.
- Step 6: checked the away-localization fraction form and the explicit exponent-decreasing substitution; the bounded monomials give a finite module spanning set, including no generators.
- New nodes: none; the item has no new-node statements requiring B1–B7 review. Existing DAG nodes were searched for the proposed finite-spectrum, minimal-prime, and locally-nilpotent facts and cited instead.
- Small cases: field base with zero prime, zero algebra, dual-number base at its minimal prime, empty generator list, and nonuniform nilpotence were checked against the statement and steps.

Changes made in this second reading: removed the worker-written `split_report.tool_uses` entry, which C8 reserves for the maintainer, and kept its justification above. Preserved `created.item`, which correctly records the parent split that originally created this existing node. No mathematical statements or proof steps required alteration. All citation quotes were compared verbatim to the existing DAG statements.
