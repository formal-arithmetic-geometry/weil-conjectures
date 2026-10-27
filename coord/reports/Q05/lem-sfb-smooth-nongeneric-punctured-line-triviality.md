# Q05 stage-1 delivery

Item: lem-sfb-smooth-nongeneric-punctured-line-triviality. Date: 2026-10-24.

## Files written

All paths below are relative to this sandbox. Six node files are under dag/nodes/sec-six-functors-basics/.

- lem-sfb-smooth-nongeneric-punctured-line-triviality.json: item, statement unchanged, five-step split.
- lem-sfb-smooth-closure-fibre-avoidance-neighbourhood.json: statement-only geometric preparation; no Mathlib match.
- lem-sfb-normal-arithmetic-closed-pair-approximation.json: statement-only normal arithmetic approximation of the pair, including completions and limits; no Mathlib match.
- lem-sfb-smooth-pair-closed-fibre-local-preparation.json: statement-only specialization and local algebra preparation; no Mathlib match.
- lem-sfb-formally-smooth-ramanujam-samuel-localization.json: statement-only local formally smooth Ramanujam--Samuel input, with analytic normality and finite residue extension; no Mathlib match.
- lem-sfb-punctured-picard-local-extension-criterion.json: statement-only generic local-to-global extension criterion; no Mathlib match.

Also report.md, citations.json, the unmodified search-tool log searches.jsonl, and write_split.py (sandbox preparation script). Only the six JSON node files and the report/citation material are delivery content. No Lean or repository file was written; no git, compiler, Lake, or build command was run.

## Attachments

None. Searches of lean/WeilConjectures by exact blueprint tag, parafactorial, Ramanujam, Samuel, punctured Picard, and smooth punctured-spectrum concepts found no finished declaration of this item. The ordinary affine/punctured-line Picard calculations are different statements.

## WANTED

WANTED: EGA IV, fourth part, §§21.13–21.14, for this item and all five new nodes; literature/ega-iv4.pdf is absent. I read these sections in the online English EGA translation at https://jcreinhold.github.io/ega/iv/34-ch4-21-divisors.html, extracting the complete §21.14.3 proof and §§21.13.1, 21.13.8, 21.13.10, 21.14.1–21.14.2. The web renderer rejects this large page, but a read-only Python HTTP fetch and standard-library HTML parser returned the relevant text. Nothing was downloaded into the repository. The proof is marked agent assembly and the missing local source is explicit.

## What was wrong and what changed

The imported item had no proof. Its statement accurately records the FIRST assertion of EGA IV4 21.14.3(i) and is retained. In particular, it is not the second assertion about prime cycles and cannot be proved by applying its parent divisor node (which already depends on it).

The important hypothesis trap is that EGA 21.14.2 assumes analytic normality of the base local ring and finiteness of the residue extension at its auxiliary local ring B. Neither is available at the original point. I follow 21.14.3's arithmetic approximation and closed-specialization proof, instead of silently applying 21.14.2 at the original x. The local ring at z is a localization of the local ring at a closed specialization y in the SAME fibre. The finite residue extension is at y; the original residue extension can be transcendental.

There is no statement dispute, no change to the chapter or unit, and no route substitution. I read the chapter and unit records and the current latest blueprint's sk-thm-sf-ctf-stability unit and direct-images proof (3). The inherited null blueprint.from.node is confirmed by blueprint_refs.py ancestor. Each new from.via prepends this item to the existing chain; each from.place identifies its exact lower EGA input. Whole-blueprint searches for parafactorial, Ramanujam, punctured spectrum, punctured local, normal arithmetic, normal domain, closed specialization, fibre component, formally smooth, line bundle, and invertible extension did not find the five statements. same_as is empty.

## Searches and candidate assessment

Every new node records two genuinely run LeanFinder phrasings, one LeanSearch query, Loogle, and Mathlib grep, drawn verbatim from searches.jsonl. All these services answered successfully. The arithmetic node additionally records the normal-ring Loogle query and the grep locating Algebra.Smooth.exists_subalgebra_fg. I read Mathlib/RingTheory/Smooth/NoetherianDescent.lean:214–217: it supplies a finite-type smooth model but no normal subrings, closed-pair fibre avoidance, generic codimension, or normal completions. It is therefore not the approximation lemma in one line. The other hits were smooth chart theorems, fibre Jacobsonness, generic-point definitions, and stalk specialization maps, not the stated preparation lemmas.

I read Mathlib/RingTheory/PicardGroup.lean:537–547: triviality of Pic(R) for a local or semilocal ring is about modules on the whole affine spectrum and gives no triviality on the punctured spectrum. This is not a match for either the item, the Ramanujam--Samuel lemma, or the local extension criterion. The grep for parafactorial and punctured Picard was empty. No node is marked mathlib.

## Not duplicates

lem-sfb-smooth-closure-fibre-avoidance-neighbourhood vs lem-sfb-smooth-nongeneric-punctured-line-triviality: the new node produces an affine closed pair and fibre/generic-codimension hypotheses; it asserts nothing about line bundles.
lem-sfb-normal-arithmetic-closed-pair-approximation vs lem-sfb-smooth-nongeneric-punctured-line-triviality: the new node constructs normal arithmetic models of any supplied closed pair; it asserts no Picard triviality.
lem-sfb-smooth-pair-closed-fibre-local-preparation vs lem-sfb-smooth-nongeneric-punctured-line-triviality: the new node supplies a closed specialization, local map and primes, without any line-bundle conclusion.
lem-sfb-formally-smooth-ramanujam-samuel-localization vs lem-sfb-smooth-nongeneric-punctured-line-triviality: the new node is the local algebra theorem EGA 21.14.2, with analytic-normality and finite residue-extension hypotheses absent from the item; applying it requires arithmetic approximation and closed specialization, not a renaming of x.
lem-sfb-punctured-picard-local-extension-criterion vs lem-sfb-smooth-nongeneric-punctured-line-triviality: the new node assumes punctured-Picard triviality everywhere on a closed subset and derives extension; it does not prove that hypothesis for smooth morphisms.
lem-sfb-normal-arithmetic-closed-pair-approximation vs lem-sbc-normal-pointed-family-approximation: the existing result requires a section and geometrically connected fibres, produces normal Noetherian schemes rather than normal finite-type integer subrings, and does not retain a closed subset or analytic normality.
lem-sfb-normal-arithmetic-closed-pair-approximation vs lem-sbc-normal-noetherian-refinement: the existing result refines a supplied base approximation, without smooth closed pairs, integer models or normal completions.
lem-sfb-normal-arithmetic-closed-pair-approximation vs lem-sfb-group-open-arithmetic-model: the existing result requires a group and a fibrewise nonempty open, and gives neither normal models nor the closed-pair codimension conditions.
lem-sfb-normal-arithmetic-closed-pair-approximation vs lem-per-henselian-normal-completion-preparation: the latter has an already quasi-excellent local input and produces henselizations/normalizations; it supplies no arithmetic pair approximation.
lem-sfb-smooth-pair-closed-fibre-local-preparation vs lem-per-locally-noetherian-closed-specialization: the existing result gives a closed specialization, but not the finite residue extension, formal smoothness, prime comparison, or dimension statements needed here.
lem-sfb-smooth-pair-closed-fibre-local-preparation vs lem-sc-finite-type-nonclosed-closure-closed-points: the existing lemma assumes an algebraically closed ground field and produces infinitely many closed points, without any of the relative local algebra data.
lem-sfb-smooth-pair-closed-fibre-local-preparation vs lem-sfb-smooth-stalk-formally-smooth: the latter gives only formal smoothness of a supplied stalk map, not a closed specialization, finite residue extension, or the two primes and their dimensions.
lem-sfb-punctured-picard-local-extension-criterion vs lem-sfb-parafactorial-principal-cycle-extension: the existing result extends principality of a supplied codimension-one cycle, rather than arbitrary invertible sheaves on an open complement; the statements are not interchangeable.
lem-sfb-punctured-picard-local-extension-criterion vs lem-trf-invertible-affine-limit-descent: the latter descends a module to a stage of an inverse system, not across a closed subset. It is reused, not duplicated.

All five new nodes vs lem-sfb-ramanujam-samuel-prime-divisor and lem-sfb-smooth-normal-affine-boundary-cartier: the existing nodes give Cartier equations for divisors or affine boundaries and depend on this item's punctured-local input. None supplies its geometric preparation, arithmetic approximation, formal local algebra theorem, or arbitrary-line-module extension. Citing them here would introduce a dependency cycle.

## Review by Q05

I read delivery-errors B–E in full and reviewed the six statements and the proof with those specific errors in mind. All five new nodes have statements only, no proof sketch in the statement, their own objects and hypotheses, actual search records, inherited chapter/unit, and precise EGA sources. No SGA source is used. A Stacks tag is not invented for the Ramanujam--Samuel result: EGA 21.14.1/2 is its source. For the existing generic inputs, I read Stacks limits.tex lemma-descend-invertible-modules, Tag 0B8W, and descent.tex lemma-normal-local-smooth, Tag 034F. The sources of the new lemmas are the EGA places listed individually above and in their source fields.

Step 1 uses exactly the neighbourhood lemma's output and the arithmetic approximation lemma's hypotheses. The former gives the normal affine domain, smooth finite presentation, fibre-component avoidance and generic-fibre codimension; the latter accepts exactly these. It is not a local Picard theorem hidden in a new node. No conclusion about completions is made for the original base.

Step 2 uses the literal localization definition and the existing invertible-affine-limit-descent statement. I wrote the puncture identification: a prime contained in r and containing r is r. Finite generation of r gives a finite principal-open cover on which the inverse-limit construction is localization. The reverse-neighbourhood index is a set, nonempty and directed by multiplying denominators. Every W_t is a Noetherian separated quasi-compact open and the transitions are base changes of principal open immersions, hence affine. These are all hypotheses of the cited descent theorem, not just a definition node cited for an existence theorem. Descending L to W_t and shrinking V preserves both geometric hypotheses.

Step 3 uses the arithmetic node's explicit qcqs/affine-transition inverse system of complements. It then invokes the existing descent theorem a second time to descend the particular invertible sheaf to one stage. This avoids an uncited assertion that arbitrary line modules automatically descend. I corrected the arithmetic statement during self-review to say explicitly that its V_i and W_i are Noetherian and to cite the definitions for quasi-compact, quasi-separated and affine.

Step 4 uses the local-preparation node's actual stalks and strict prime containment, not the proof of that node. Its q_z strictly contains p, so q_z is not contained in p. The arithmetic statement explicitly supplies the normal completion of A', which is the missing hypothesis of the local Ramanujam--Samuel theorem. The latter gives triviality of every punctured local invertible module. The existing smooth-normal-ascent statement gives normality of V_i; arithmetic approximation gives Noetherianity; local preparation gives local dimension at least two on Z_i. Thus the hypotheses of the local-extension criterion all hold, and its essential-surjectivity clause extends the supplied L_i to V_i. No theorem about prime cycles is used as though it extended arbitrary line modules.

Step 5 is elementary from the two cited definition statements: tensor pullback preserves a local rank-one trivialization, and an invertible module trivializes on some neighbourhood of x. All primes in Spec O_{V,x} are generalizations of x and hence lie in that neighbourhood. Pulling back its trivialization proves the item. I have checked the full verbatim statement quotes in citations.json for every occurrence of a proof citation; each is an exact substring of the cited node's statement. No use relies on a proof-only construction. proof_deps is exactly the union of uses, and no new dependency points back to the item or its divisor parents.

Small cases and necessity checks: over a field, a nongeneric point of local dimension one is excluded by the explicit dimension assumption; over a field in local dimension at least two the theorem agrees with regular-local factoriality. In relative dimension zero there are no nongeneric smooth-fibre points, so the item is vacuous. A DVR base with a closed point on a smooth relative curve gives the expected two-dimensional regular local case. A singular normal base is permitted: its divisor classes do not force a nontrivial line module on the whole puncture, because the corresponding pulled-back divisorial module can fail to be invertible at the fibre-generic prime that remains in the puncture. A transcendental original residue extension is allowed because the finite extension is only introduced at y after specialization. Empty closed sets and empty generic intersections are explicitly harmless. The local formal theorem excludes dimension-one punctures and keeps the strict q-not-contained-in-p condition. The generic extension criterion is not asserted in dimension one, where removal of a Cartier point would not be fully faithful.

No proof step exceeds 2000 characters. New nodes are not elementary two-line consequences or clauses of the item: they isolate the five independent EGA inputs, and the assembly performs descent twice, obtains the local hypotheses, extends the actual module and pulls it back to the puncture. The off-unit limit-descent node is a generic tool and is declared in split_report.tool_uses. The tools check_dag and review_split have already passed on the server; the full deliver.py dry run and push follow this signed review.

## Unfinished work

No stage-1 work remains in the assigned item. The five new nodes deliberately remain unsplit for later workers. The local EGA IV4 copy remains WANTED. Delivery is subject to the full dry run and maintainer's independent mathematical review.
