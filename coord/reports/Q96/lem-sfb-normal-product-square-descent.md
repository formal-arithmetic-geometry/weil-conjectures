## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-normal-product-square-descent.json`: statement, now split; no exact project attachment or Mathlib match found. The statement and its statement dependencies are unchanged. Four proof steps reuse existing nodes.
- `citations.json`: ten entries, one per step/node citation, with verbatim substrings of the cited statements.
- `report.md`: this report. `searches.jsonl` was written by the required search command.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched `lean/WeilConjectures/` by the exact item tag and by theoremOfSquare, square-difference and normal-product-square/descent terms. The only square/descent hit was the unrelated finite-chain-square colimit module. Nothing found states the item's conclusion. No Lean files were written or compiled.

## Wanted literature

WANTED: Ning Guo, *Divisors on coherent schemes and homogeneous spaces*, March 31, 2026 author version, Proposition 5.2(i), printed p.11 (and Corollaries 3.9, 3.12, printed pp.7-8), for lem-sfb-normal-product-square-descent. The repository has no local PDF. I read the author's online PDF at https://ningguomath.com/wp-content/uploads/2026/03/amplenew-1.pdf without downloading it into the repository. The actual general descent input used here is available locally as Stacks Tag 0BD7 in `literature/stacks-project/divisors.tex`.

## Findings and corrections

The imported statement is correct. Guo's parameter space is written as W times W with W=X1 times X2; regrouping its factors gives the item's P. The parity signs of the four summands agree with the displayed D(A). Smooth finite-presentation factors over the stated normal Noetherian base fall within the intended specialization. The argument requires neither a section of X3 nor properness nor extension of the particular N_eta.

Reused `lem-sfb-normal-noetherian-generic-line-pullback` rather than creating another generic-line descent result. I read its complete statement and proof against Stacks 0BD7, `lemma-in-image-pullback`, including all five hypotheses. The projection's base is P, so triviality must be checked over the generic point of P; triviality over S's generic fibre is not assumed. Step 3 supplies precisely this reduction from the given pulled-back line N_eta.

The item's inherited blueprint endpoint was null. `blueprint_refs.py ancestor` consequently printed None. I followed every `created.item` link through the supplied via chain to `lem-sfb-admissible-direct-image`, whose existing blueprint endpoint is `det-thm-sf-ctf-stability-direct-images`, and used that endpoint while retaining the via chain. I read the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-image proof (3). This remains a supporting geometric input on its inherited local-ample-line branch; no unit or chapter is edited.

## Searches and reuse

Whole-DAG searches included the item id, Guo, 0BD7, lemma-in-image-pullback, generic-line pullback, vertical Cartier descent, smooth base change and composition, and geometric integral/connected product terms. Whole imported-blueprint searches used `blueprint_refs.py search` with square, square difference, generically trivial, integral fibres, smooth morphisms and geometrically integral product. No imported blueprint node states the item. The general 0BD7 node already supplies the descent input; the vertical-group Cartier node has extra group/section structure and is unnecessary.

Ran the prescribed Mathlib search command for the item with LeanFinder twice (generic-line descent and mixed tensor cross difference), LeanSearch, Loogle and grep. All five calls succeeded, and their actual queries/results are recorded from `searches.jsonl`. Read the returned signatures: normalizationDesc and normalizationDiagram concern normalizations of scheme maps; the pullback-triplet declarations construct residue-field tensor-product geometry; the descendsAlong hits concern properties of scheme morphisms, not line modules; sq_tsub_sq is a scalar-ring identity. Loogle and the targeted AlgebraicGeometry grep returned no hits. None is an exact match or a one-line specialization of this item. The earlier Q138 search records remain intact.

## Review by Q96

I checked delivery-errors B through E with the source statements open. No new nodes are created, so there are no statement-only-node, missing-search or duplicate-node obligations to defer. The statement is unchanged and self-contained; the invertibility, residue-field-fibre and normality meanings are explicit. Every proof dependency is the union of the uses lists. The four step lengths are 1217, 618, 1043 and 480 characters, so no long step conceals an independently formulated lemma.

For the item I read Guo Proposition 5.2(i), its definition of the square in section 5.1, and the generic-trivial-line Corollaries 3.9/3.12 online. The reduction is the same: evaluate at the generic point of the parameter space, trivialize the line over that field, and descend. I also read Stacks divisors.tex, Tag 0BD7, locally, and its existing DAG node. The paper's last displayed conclusion in the proof of (i) writes L where its argument concerns s(L); I use the square-difference line M throughout. This typographical issue does not change the proposition or the imported item.

Step 1 uses clause (2), specifically smooth base change, of `lem-pc-proper-base-change`; the complete statement explicitly includes this clause, unlike a theorem only about proper morphisms. I read the local Stacks 01VB lemma-base-change-smooth as well. Each new factor's fibre over b is obtained from the original residue-field fibre by the field extension kappa(s) to kappa(b). The hypothesis quantifies over every field extension, so it gives nonempty integral fibres, including geometric connectedness. Applying `lem-sbc-smooth-connected-generic-geometry-core` successively is legitimate: at each stage the preceding base is normal integral and the source is nonempty. That node explicitly concludes both integrality and integral closedness of every local ring. I read Stacks 034F lemma-normal-local-smooth and 056T lemma-smooth-geometrically-normal supporting its geometric hypotheses. For local Noetherianity, `lem-pc-smooth-flat` explicitly gives local finite presentation, hence local finite type by forgetting the finite list of relations; `pqf-lem-locnoeth-lft` then gives exactly local Noetherianity of the next stage. I read Stacks 01T6 lemma-finite-type-noetherian. No theorem about products of integral schemes over a field is implicitly used; building P by these smooth families avoids such an extra input.

Step 2 uses the same smooth-base-change, smooth-flat/lfp and locally-Noetherian/lft statements for pi and its source Y. I separately checked its fibres at arbitrary p in P, whose residue fields may strictly extend kappa(s); geometric integrality, rather than integrality alone over kappa(s), supplies the required integral nonempty Y_p. The locally-of-finite-type alternative of the descent theorem is available. Thus no global Noetherianity, quasi-compactness of S, excellence or regularity of S is inserted.

Step 3 is elementary from the two cited definitions. `def-pc-module-pullback` explicitly includes composition functoriality; its tensor formula explains the pullback of local frames. `def-sc-invertible-module` explicitly means Zariski locally free of rank one. Over a field such a module has a nonzero basis. The generic point xi of P maps to eta because P to S is surjective and continuous: all images are specializations of the image of xi. Consequently xi factors through P_eta, and pulling back the supplied isomorphism gives M restricted to Y_xi as the pullback of a one-dimensional vector space. This is a genuine trivialization on the entire generic fibre of pi. Pullback and tensor of local rank-one frames also show that D(A) is invertible; this is not inferred merely from a definition of a Picard group. No compatibility of chosen trivializations or global choice of N_eta's frame is needed.

Step 4 uses exactly the statement of `lem-sfb-normal-noetherian-generic-line-pullback`, not any construction hidden in its proof. I matched its five hypotheses to steps 1-3 individually, and its concluding f-star N isomorphic to M supplies all of the requested conclusion upon reversing the isomorphism. This existing node is in the same unit. The two off-unit non-leaf geometry facts are declared as generic tool uses in split_report; the remaining off-unit theorem citations are existing Mathlib leaves, and the two definition citations supply only notions.

Small cases checked: if S is a field, xi is still the generic point of P, and the supplied N_eta is already a line on P; the generic-point argument remains valid. If X1 or X2 equals S, the four factors cancel in pairs, as expected. If X3 equals S, pi is the identity and the conclusion is automatic. Empty fibres are excluded by the stated geometric-integrality convention, so every surjectivity and nonemptiness inference is valid. A nonproper X3, such as an affine-line family, creates no obstruction: 0BD7 requires flat integral fibres and local finite type, not properness. A normal singular base is allowed because normality is preserved by smooth maps and no Weil-divisor-to-Cartier assertion over a regular base is used. These checks required no statement repair.

No SGA source is cited. No new-node cycle can arise; all reused nodes were read, and none of their dependency paths points to this newly created descendant item. citations.json was generated only after asserting that each quote is a literal substring of the relevant current statement.

## Unfinished work

None in the requested one-level split. Existing dependency nodes retain their own stage states. The local copy of the Guo paper remains a literature request; the proof's general descent theorem is already present in the repository as Stacks 0BD7 and the reused DAG node.
