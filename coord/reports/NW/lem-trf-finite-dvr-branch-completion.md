# Worker report: lem-trf-finite-dvr-branch-completion

## Files written

- `dag/nodes/sec-trace-formula/lem-trf-finite-dvr-branch-completion.json`: existing statement node, now split in six steps; not a Mathlib leaf.
- `citations.json`: thirteen exact statement quotations, one for every step/node pair.
- `report.md`: this report. The search command maintains `searches.jsonl`.

New nodes: 0. New Mathlib leaves: 0. Existing Mathlib leaves used include completion flatness, PID normality, localness of completion, finite-algebra integrality and finite-algebra Noetherianity.

## Attachments

None. Searches of `lean/WeilConjectures/` for the exact blueprint tag and branch/completion terminology did not find a declaration stating the whole item. The finite-completion declarations give only the product clause, and the curve-branch declarations concern henselian normalization branches rather than this arbitrary finite algebra. No sorry-containing declaration is treated as a finished proof.

## WANTED

None. The sources needed here are present locally.

## Findings and changes

The live item had no proof. I preserved its complete statement and statement dependencies and supplied the finite-completion argument from Stacks 0C3V's final paragraph, with its auxiliary results 07N9 and 0AP1. No statement dispute was found. The extra conclusions are proved explicitly: flat base change gives the tensor injection; nilpotence descends through it; finite generators base-change; and a monic equation can be checked in each fraction field. This does not assert birationality or identify Q(C) with Q(R), which do not follow merely from finiteness and injectivity and are not needed by this item.

The sources and tags were checked against `literature/stacks-project/tags/tags`. I corrected my draft's mistaken PID-normality tag to 00GZ (lemma-PID-normal). No repository or launcher file was changed, and no compiler, Lake command or sub-agent was used.

## Searches and reuse

I read and retained the item's earlier Mathlib search records, including its unavailable LeanSearch result. Five new searches were run by the required msearch command and recorded with the exact query strings and outputs in the item and searches.jsonl: two different LeanFinder phrasings, Loogle `AdicCompletion, Module.Finite`, one Mathlib/RingTheory grep, and LeanSearch. The services answered for these calls. Loogle and LeanSearch found the finite-module tensor/completion equivalence; I read AsTensorProduct.lean at 321--340. It does not give the product of localized completions and all the DVR and normality conclusions. LeanFinder returned the valuation completion of a Dedekind fraction field; I read AdicValuation.lean at 576--624 and did not conflate it with ideal-adic completion. The grep returned no hits. No hit states the item or specializes to all its clauses in one line.

DAG searches by completion terminology and tags 07N9, 0AP1, 00MB and the PID-normality source found existing generic lemmas, all reused. Blueprint searches were run for completion, DVR, completion/finite, completion/valuation, normal-ring integral closedness, and finite-product normality; none states this complete finite-algebra assertion. `blueprint_refs.py ancestor` confirmed lem-trf-local-term-locality. The inherited ancestry and its exact auxiliary-input place were retained; same_as is empty. I read the chapter/unit records and the current main-20261015 ancestor text. This is a commutative-algebra auxiliary on the existing route, not a replacement of a chapter or unit argument.

## Not duplicates

No new nodes were created. In particular I reused lem-weil-pbc-completion-finite-extension and lem-weil-pbc-completion-of-dvr-is-dvr instead of creating duplicate product-completion or DVR-completion nodes. Nilpotence in a product, base change of a finite generating set and the coordinate fraction computation remain elementary arguments in the item.

## Review by NW

I read Stacks varieties.tex, Tag 0C3V (lemma-normalization-same-after-completion), especially the final displayed product and the subsequent DVR-completion argument. I also read algebra.tex, Tag 07N9 (lemma-completion-finite-extension) and its proof, 00MB (lemma-completion-flat), 00MC, 00GZ (lemma-PID-normal), 00GK (lemma-finite-is-integral), 00FN (lemma-Noetherian-permanence), and the integral-closure and fraction constructions. In more-algebra.tex I read 07NV (lemma-completion-dimension), 0AP1 (lemma-completion-dvr) and the neighboring regular-completion argument. There are no new statement-only nodes requiring separate source review.

For step 1 I opened lem-weil-pbc-completion-finite-extension. Its statement gives finiteness and the algebra isomorphism simultaneously compatible with the finite algebra and the completed base, rather than merely an abstract ring isomorphism. Its hypotheses are exactly a Noetherian base, a finite ring map and a prime. Our maximal ideal is prime; localization of the local base is identified explicitly, and tensor symmetry changes the order of the factors with the displayed coordinate formula.

For step 2 I opened def-sc-discrete-valuation-ring, lem-weil-pbc-completion-of-dvr-is-dvr and lem-weil-pbc-pid-noetherian-normal. The definition includes the Noetherian local-domain/principal-maximal-ideal characterization needed to apply the completion lemma. The assumption already supplies a DVR at each indexing prime, so neither normality nor dimension of B is inferred from finiteness alone. The PID leaf supplies normal-domain integral closedness, not the converse of a DVR characterization. No excellence or characteristic assumption is imposed or used.

For step 3 I opened lem-weil-pbc-noetherian-completion-flat and def-weil-pbc-flat-ring-map. The former gives flatness for any ideal of a Noetherian ring; the latter explicitly defines flatness by preservation of injections. Thus this use does not hide an uncited tensor-exactness theorem. The scalar/unit tensor identification is written down and identifies the resulting injection with the required structural map. Step 4 is elementary: a nilpotent tuple vanishes coordinatewise in domains, and the injective map detects zero in the base.

For step 5 I opened all five cited nodes: adic-completion-noetherian, local-completion-local-ring, completion-dimension, finite-algebra-is-integral and finite-algebra-noetherian (all with prefix lem-weil-pbc-). They respectively supply the completed base's Noetherianity, localness, unchanged dimension, and the finite algebra's integrality and Noetherianity. I checked the latter two only after the proof explicitly supplies a finite R-generating set for C. No finiteness of residue fields is needed.

For step 6 I opened def-weil-pbc-module-localization and def-weil-pbc-integral-closure. Their fraction equivalence and monic-equation definition justify the entire elementary calculation: regular denominators have nonzero coordinates by the one-coordinate tuple test; projection preserves the monic equation; step 2 puts each coordinate fraction in its ring; the tuple of those elements satisfies c=sd. This proves integral closedness in the actual total ring of fractions without assuming C is a domain or hiding a product-of-fraction-fields isomorphism. Full verbatim statement quotations for every citation are in citations.json; no proof of a cited node is used as an additional conclusion.

I tested A=B a DVR, which gives a single completed DVR, and the two-branch node A=k[[u,v]]/(uv) with B=k[[u]] times k[[v]], which checks that the base need not be a domain. Injection is essential: if A=k[t]_(t)[e]/(e^2) and B=A/(e), the branch is a DVR but the completed base is not reduced. A field factor would violate the explicit DVR hypothesis rather than supply an overlooked zero-dimensional case. The zero ring cannot be a base of dimension one. None of the non-elementary steps exceeds 2000 characters; each elementary calculation is fully written and introduces no independent hidden lemma.

The four non-leaf tools from sk-thm-p1 are declared in split_report.tool_uses: finite-completion decomposition, DVR-completion preservation, completed-base Noetherianity and completion dimension. They are generic algebra inputs absent from this unit's own statements. Definitions and existing Mathlib leaves need no route exception. No SGA source is cited.

## Unfinished work

No mathematical part of this one-level split is left open. The already-existing dependency nodes retain their own stage states. Delivery validation is recorded below when complete.
