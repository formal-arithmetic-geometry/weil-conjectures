## Files written

- dag/nodes/sec-deligne-laumon-a1/lem-per-semilocal-jacobson-completion-product.json: item, statement, split into eight explicit steps; no exact Mathlib match.
- citations.json: verbatim statements for every node used in each step.
- No new nodes and no new Mathlib leaves. The two existing theorem leaves and two existing definition leaves suffice.

## Attachments

None. Searched lean/WeilConjectures for the exact blueprint tag, semilocal/semiLocal, Jacobson completion, and completion/product expressions. GRingNagata and the other semilocal files do not give this completion comparison. No project declaration stating all clauses was found.

## WANTED

None. All source material used is present in literature/stacks-project/algebra.tex.

## Corrections and source qualifications

The item's statement and statement dependencies are unchanged. The imported node had no proof. Tag 07N9 (algebra-lemma-completion-finite-extension), lines 23135–23175, treats a finite algebra over a localized Noetherian base; it is source material for the quotient-product/inverse-limit argument, not a theorem directly applicable to an arbitrary semilocal ring. I wrote the CRT variant explicitly and marked proof_origin as agent. No finite-algebra-over-local-base hypothesis is assumed in the split. The Noetherian hypothesis is retained although this elementary argument does not require it.

The existing leaf lem-pc-crt-ideal-quotient-product has the right mathematical statement and exact Mathlib declaration Ideal.quotientInfRingEquivPiQuotient (Mathlib/RingTheory/Ideal/Quotient/Operations.lean:248). Its source place incorrectly calls the CRT tag 00U3. The correct tag is 00DT, label algebra-lemma-chinese-remainder, verified against stacks-project/tags/tags and algebra.tex:2615–2663. My step sources use 00DT; I did not change the existing node.

## Searches and blueprint route

Read the item's inherited search results, then ran Q13 searches with msearch.py: LeanFinder on the Jacobson-radical product statement and on the finite-intersection/CRT phrasing; LeanSearch on completed maximal localizations; Loogle on AdicCompletion, Ideal; and grep in RingTheory/AdicCompletion. Read the returned hits. AdicCompletion.piEquivOfFintype, inspected in Functoriality.lean:310–319, uses one fixed ideal and an already given product of modules. It does not identify Jacobson completion with the product of completed localizations. The CRT hit is reused through the existing DAG leaf. The item records the actual Q13 queries and logged results in addition to the inherited Q31 searches.

Searched the whole DAG by Chinese remainder, pairwise coprime/comaximal ideals, powers, quotient/localization and maximal-ideal existence. Read the existing general CRT leaf and proper-ideal-contained-in-maximal leaf. Also read the 07N9 decomposition and finite-localized-quotient nodes: they impose finite-map/local-base hypotheses and cannot be specialized to this arbitrary semilocal input. No duplicate node was created. blueprint_refs.py searches for completion, Chinese, Jacobson, semilocal, coprime ideals and maximal ideals found no blueprint node stating this completion comparison. The reported nearest ancestor is lem-per-artin-gabber-affine-curve. Read that ancestor's current literature/blueprint/latest proof and the chapter and unit records; this is a supporting algebra calculation below the inherited regular-local-model chain, not a change to the Fourier-perverse unit route. The existing blueprint.from.place and via are retained; same_as remains empty.

## Not duplicates

No new nodes. In particular, I reused lem-pc-crt-ideal-quotient-product instead of creating another CRT node, and lem-weil-pbc-proper-ideal-contained-in-maximal instead of creating a maximal-ideal existence node.

## Review by Q13

I read Stacks Tag 07N9, algebra-lemma-completion-finite-extension, including the precise finite-map hypotheses and its passage from finite quotient products to the completed product. I then read all of Tag 00DT, algebra-lemma-chinese-remainder, and Tag 00E0, algebra-lemma-Zariski-topology, item (2) and the proper-ideal observation in its proof. I checked the localization fraction convention at algebra.tex:1218ff and the actual statements of both definition leaves. There are no new nodes whose sources require a separate review.

Step 1 uses exactly the existing maximal-ideal existence leaf's sentence that every nonzero commutative ring has a maximal ideal. Thus absence of maximal ideals forces the zero ring; this is not inferred merely from the definition of semilocal. With J=A its positive-power quotients and the empty product really are zero.

Steps 2 and 3 use elementary ideal calculations, with the arguments included. Distinct maximal ideals are comaximal by maximality, and expansion of (u+v)^(2n-1) proves comaximality of their nth powers for n>=1. The two-ideal intersection/product identity and the induction making a product comaximal with the next ideal are both written, so the step does not take an extra clause from the CRT node. Finite ideal-product distributivity gives J^n=intersection m_i^n. No radical-power cofinality, Artinian decomposition or completion-flatness theorem is hidden here.

Step 4 uses precisely the canonical ring isomorphism stated by lem-pc-crt-ideal-quotient-product. Its finite-family and pairwise-coprime hypotheses were verified in Steps 2 and 3. The source and the leaf state the map on a representative, so reduction compatibility is checked on that representative, rather than asserted as an unspecified naturality theorem. Respect for A follows from the same formula.

Step 5 uses the actual fractions and canonical ring map of def-weil-pbc-localization-at-prime. The finite geometric series proves every allowed denominator is a unit in A/m_i^n. Step 6 again uses that leaf's explicit equality relation: u(sx-c)=0. I checked both surjectivity and injectivity of the quotient comparison, and expanded extension of ideal powers with common denominators. The proof never cancels a possibly zero-divisor denominator in A. Maximality gives primeness for defining the localization, and positive n is maintained throughout.

Step 7 uses exactly def-weil-pbc-adic-completion's compatible-sequence description with componentwise operations. It spells out the inverse sequence via psi_n inverse. Injectivity of psi_n gives compatibility of the reconstructed sequence. Therefore there is no appeal to a missing theorem that limits commute with products. The preceding representative calculation checks the transition square for each localization-quotient map explicitly.

Step 8 uses the two definition leaves for their structural maps from A. Its displayed value on a is localization followed by completion in each factor, giving both A-linearity and the factor-map clause. It does not infer uniqueness of maps merely from agreement on a dense image.

For small cases I checked the zero ring (t=0), a field and a non-complete local ring (t=1), a product of two fields (J=0 and the result is the identity product), and a product of rings of dual numbers (nilpotents and zero divisors). The finite series and fraction-kernel arguments still hold in these cases. The restriction n>=1 avoids the zero-level quotient distraction. Every proof-step citation has its full verbatim statement in citations.json, and every uses entry is included in proof_deps. Every step is under 2000 characters. B1–B10: no new nodes or hidden proof sketches; notions reuse actual definition statements; source tags and Mathlib lines were checked; no false leaf or finished attachment claimed. C1–C8: non-elementary inputs have existing leaves, each opened and read; elementary arguments and transition checks are explicit; no new dependencies back to this item. D1–D5: the proof carries the completion argument itself rather than moving the conclusion into a new node. E1–E7: checked hypotheses, denominators, zero case, the correct localization/quotient ideals and all canonical maps. No statement dispute was found.

## Unfinished work

No mathematical part remains in this stage-1 split. Dry run and direct delivery follow this report.
