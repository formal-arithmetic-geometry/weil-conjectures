# Q55: lem-trf-etale-weakass-invariance

## Files written

- dag/nodes/sec-trace-formula/lem-trf-etale-weakass-invariance.json: item, statement unchanged, split in seven steps.
- dag/nodes/sec-trace-formula/lem-trf-finite-ring-map-weakass-contraction.json: one new statement-only unsplit lemma, no Mathlib match. Source: Stacks Tag 05E1, label lemma-weakly-ass-finite-ring-map; the contraction inclusion only, for any module over a module-finite algebra.
- report.md and citations.json: this report and the verbatim statements supporting every cited step. searches.jsonl retains the search command's original records; write_split.py is a sandbox-only preparation script.

## Attachments

None. Searched the project declarations under /home/ubuntu/weil-src-slopmaster2/WeilConjectures for the item id, weakAss, WeakAss, weaklyAssociated, weakly associated and weak assassin; also checked the read-only master reference. No declaration states the item or the proposed child. Nothing was compiled and no Lean was written.

## Wanted literature

None. All sources used were available locally in literature/stacks-project/.

## Findings and corrections

The imported item was true and had no proof. Its statement, arbitrary-module quantifier, and absence of Noetherian assumptions are preserved. The previous Mathlib searches and blueprint provenance are retained. No target or unit statement has changed.

Read flat.tex, labels lemma-etale-weak-assassin-up-down (05FP) and lemma-finite-flat-weak-assassin-up-down (05FN), divisors.tex label lemma-weakly-ass-pullback (05F0), and algebra.tex label lemma-weakly-ass-finite-ring-map (05E1). The standard-etale reduction in 05FP and finite-free argument in 05FN are the descent route. For ascent, the localized annihilator argument of 05F0 becomes particularly explicit for an etale map because the base maximal ideal generates the target maximal ideal (existing node, Tag 00U4). This supplies the details rather than hiding the ascent clause in a new node. The finite-direct-sum weak-assassin argument is also written in the item, rather than creating an elementary node.

Mathlib's associatedPrimes in RingTheory/Ideal/AssociatedPrime/Basic.lean:62-115 is defined using prime radicals of annihilators, which does not in arbitrary rings mean all primes minimal over an annihilator. Its localization contraction lemma at Localization.lean:78-114 also assumes the contracted prime is finitely generated. These hits cannot discharge the finite-map weak-assassin lemma without extra mathematics or hypotheses. The alternative semantic search found Ideal.exists_minimalPrimes_comap_eq, which lifts minimal primes of a contraction; it supplies the opposite direction from the needed assertion that a particular minimal prime contracts to a minimal prime. Module.comap_annihilator identifies annihilators only, and associatedPrimes.finite assumes Noetherianity. Both semantic phrasings, Loogle, grep and LeanSearch are recorded exactly from searches.jsonl. Additional searches tested a general flat-ascent helper; after reading the sources I did not create it, since ascent can be carried by the item's steps.

## Not duplicates

lem-trf-finite-ring-map-weakass-contraction vs lem-trf-etale-weakass-invariance: the new result is restriction of scalars of an arbitrary S-module for a module-finite map R to S, with no etale hypothesis and no tensor base-change conclusion; it is the finite-algebra ingredient in descent, not either clause of the item restated.

lem-trf-finite-ring-map-weakass-contraction vs lem-trf-flat-tensor-weakass-fibre: the existing parent studies tensor pullback along a flat finitely presented algebra and detects the associated fibre prime; the new lemma assumes finiteness but not flatness and contracts weakly associated primes of any module. The parent depends on the present item, so citing it here would be circular.

lem-trf-finite-ring-map-weakass-contraction vs lem-sc-weakass-localization: the latter detects a prime in one ring after localization at that prime; it says nothing about restriction of scalars along finite ring maps. It is reused for localization, not duplicated.

Searched the entire DAG by Tags 05E1 and 05EZ, the label weakly-ass-finite-ring-map, and weak-assassin terminology, and searched imported blueprint statements using blueprint_refs.py search with weakly associated, finite flat, annihilator, finite ring and 05E1. No existing node states this finite-map contraction result. No pre-existing node shares its source tag. The blueprint ancestor is lem-trf-local-term-locality, with the inherited historical semistable-algebra provenance through lem-trf-flat-tensor-weakass-fibre; from.place and via retain that trace. same_as is empty after the full-blueprint search.

## Review by Q55

I read the chapter and unit records and the current main-20261015 local-term proof. The unit now uses contracting correspondences. This item belongs to an inherited historical semistable-algebra supporting branch, as its current blueprint provenance already says. I have not substituted a different unit route or used SGA. I checked the item against 05FP in flat.tex. For the one child, I read 05E1 in algebra.tex: it applies to any S-module for a finite ring map, precisely the hypothesis used on the finite algebra C, and it imposes neither a Noetherian condition nor module finiteness. The child contains a statement only, no hidden proof or proof dependencies.

For step 1, I opened lem-sc-weakass-localization and used its clause (3), not an exact-annihilator associated-prime criterion. It gives an element in L_a with radical annihilator a A_a. I opened def-weil-etale-morphism, lem-weil-pbc-flat-ring-map-iff-flat-affine and lem-weil-pbc-flat-local-ring-maps: together their statements give flatness of A_a to B_b. The last node's optional Noetherian conclusion is not used. This avoids assuming the affine stalk identification as an uncited theorem. The localization criterion is an off-unit generic tool and is declared in split_report.tool_uses.

For step 2, def-weil-pbc-flat-ring-map explicitly defines flatness by preservation of injections under tensoring. Its actual statement therefore suffices for R/I to M; I am not citing only a definition for an unprovided exactness theorem. The quotient-tensor isomorphism and the localized tensor isomorphism are given by inverse formulas, checked against the tensor relations in def-weil-pbc-module-tensor-product and the fraction relations in def-weil-pbc-module-localization. They need no finite generation or faithful-flatness assertion. In particular, the annihilator of x tensor 1 is exactly IS, not merely an inclusion.

For step 3, I opened lem-weil-pbc-etale-prime-generates-maximal: its statement is exactly a B_b = b B_b, with contraction a, which is the equality the step needs. Extending a A_a to B_b yields the same ideal since every element outside a maps to a unit. The finite-sum power expansion proves the radical equality explicitly; it does not interchange an infinite intersection and a localization. I then use the same clause (3) of lem-sc-weakass-localization to return to the global module. This supplies the ascent without making a child that just repeats that clause.

For step 4, I opened lem-weil-pbc-etale-locally-standard: it supplies an A-algebra presentation after inverting one g outside b, with a monic f over A itself; there is no unjustified change of the base ring. I opened lem-weil-pbc-monic-quotient-free: its statement gives the finite power basis of C. The prime of B_g and its contraction in C are described by the numerator criterion from def-weil-ring-localization-away, so the base contraction remains a. Degree zero would make C the zero ring and is impossible in the presence of that prime.

For step 5, I use only lem-sc-weakass-localization and the definitions of localization and tensor product. I wrote the inverse fraction maps for successive localizations and for localization of a tensor product. These identify the local modules and their local coefficient rings, so they carry annihilator radicals to the corresponding maximal ideal. Thus the existing localization theorem really gives weak association over C, not merely over the localization C_h. This is the relevant local comparison in 05FP and is written in the item's proof.

For step 6, the new finite-map contraction statement applies to K = L tensor C because C is finite over A by step 4. Its S-module P is K, with no finiteness assumption on P. Its prime is r and its contraction is a. The child asserts exactly that a is weakly associated to K restricted to A; it does not yet assert the desired conclusion about L.

For step 7, the tensor universal property gives the finite coordinate description using the already supplied basis of C. I checked the annihilator is the finite intersection of the coordinate annihilators. Primality chooses one coordinate annihilator contained in a, and minimality over the intersection forces minimality over that coordinate annihilator. This is an elementary finite-product argument, carried in the item, not a new node.

I checked B the zero ring and A the zero ring: there is no prime b, so the universally quantified statement has no instance. For L = 0 all weak-assassin sets are empty. For A = B the identity, both implications reduce to the same localization witness. A positive-degree monic polynomial gives a finite free algebra even when its quotient is nonreduced; the finite-map contraction child does not require etaleness of C. For example C = k[t]/(t^2) is permitted in that child. The finite-algebra child excludes arbitrary nonfinite localizations, where weak-assassin contraction can fail; no such generality has been asserted. A zero module in the child has no witnessing prime. The finite-coordinate argument handles zero coordinates (annihilator the whole ring), and n = 0 cannot occur in step 4 because there is a prime r.

Every cited node's complete statement was read and copied verbatim into citations.json. All seven steps are below 2000 characters; the potentially nontrivial finite-map assertion is its own unsplit lemma, while the comparisons have explicit mutually inverse formulas. The original item is neither weakened nor moved wholesale into the child. There is no dependency on a parent, no new elementary node, no claim of a nonexistent Mathlib match, and no unrun search recorded. Only the sandbox was written.

## Unfinished work

The new finite-map contraction lemma is deliberately unsplit, as a stage-1 child. No part of this item's proof remains implicit beyond that cited statement and the existing dependencies. The resumed dry run found one missing definition citation in the new child. I repaired it as detailed below; server checks and delivery are being rerun.

## Resumed review and preflight repair, 2026-10-19

The initial resumed preflight rejected the new child because its statement cited no definition node. I opened def-weil-finitely-generated-module: its first clause defines a finite module over an arbitrary ring by a finite spanning family. I cited precisely that clause at the child’s hypothesis that S is finite over R and added the definition to stmt_deps. Its later clauses about finite rings and fields are not assumptions of this child. The mathematical proposition is unchanged, and weak association and restriction of scalars remain explicitly defined in the statement. I refreshed the step-6 quotation in citations.json.

I independently reread Stacks 05FP and 05FN in flat.tex, 05E1 and 0566 in algebra.tex, and 05F0 in divisors.tex, and verified the tags against tags/tags. I reopened every proof dependency’s statement and checked all 18 step/node quotation pairs against the current files. The item’s statement still agrees verbatim with the repository. All seven steps have fewer than 1100 characters. The flatness definition explicitly preserves injections, so step 2 does not assume an uncited exactness theorem. The standard-etale presentation and the finite power basis used in step 4 are both supplied by the cited statements. The single unsplit child is the genuine finite-pushforward ingredient of 05FN, rather than either implication of the etale item.

The attachment search in both read-only project sources found no weak-assassin declaration. Existing search records were retained and read, not rerun: Mathlib’s radical-annihilator association and finitely generated-prime localization results do not cover this arbitrary-ring weak-association statement. I inspected Ideal.exists_minimalPrimes_comap_eq at MinimalPrime/Localization.lean:116: it lifts a minimal prime of a contracted ideal, whereas the needed finite-map result contracts a specified weakly associated prime. I also reran the full-DAG exact-tag searches for 05E1 and 05EZ and the whole-blueprint searches for 05E1 and weakly-ass-finite-ring-map; none supplies the child. The main-20261015 local-term source still uses contracting correspondences; the inherited historical provenance is preserved without altering that unit. The zero-ring, zero-module, identity-map, and nonreduced finite-algebra checks described above still apply after this citation repair.
