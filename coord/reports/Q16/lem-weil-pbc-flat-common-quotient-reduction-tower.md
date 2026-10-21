# Q16 stage-1 delivery: lem-weil-pbc-flat-common-quotient-reduction-tower

## Files written

- `dag/nodes/sec-proper-base-change/lem-weil-pbc-flat-common-quotient-reduction-tower.json`: existing statement, now split in six steps; Mathlib search finds no match for the whole sheaf-module derived strict-tower assertion.
- `citations.json`: verbatim statement quotes for every step/node citation.
- `report.md`: this report. `searches.jsonl` records the actual Q16 search calls; the item's inherited NE search records are retained. `write_split.py` is sandbox-only preparation, not part of the DAG delivery.

No new nodes; no Mathlib leaves created. No Lean written, no compiler invoked, no repository writes or direct git commands.

## Attachments

None. Searched all `lean/WeilConjectures/` for the blueprint id and common-quotient/restriction/K-flat notions, then inspected the possible hits. `DepthThreeCompletedQuotientLift.lean` concerns finite etale covers of a punctured spectrum, not module reduction. `CompactSupportCoefficientChange.lean` concerns compact-support projection formulas for finite constant rings. Neither states this arbitrary ring-sheaf comparison, including its strict tower and cone clauses.

## WANTED

None. All source documents used are present.

## Problems found and changes

The item had a complete intended statement but no proof. Its strict-tower meaning was implicit: I added the existing generic inverse-system definition and specified that the objects are cochain complexes and the cone comes from the constant tower. This clarifies the existing conclusion; no mathematical hypothesis or conclusion is changed or weakened. The imported fields and earlier searches remain intact.

The proof is marked agent-written: Stacks 099L gives the constant-to-completed common-quotient setting, not this general arbitrary-ideal-sheaf assertion with every strict normalization formula already written. The generalization and the formulas are supplied in the six steps; K-flat existence and descent are separately cited tools.

The site need not have enough points, and quotient sheaves need not be quotients on every set of sections. Step 2 deliberately constructs maps using tensor and sheafification universal properties and local representatives. No global lift of a quotient section is used. Likewise the ring map need not be faithfully flat, the ideals need not be finitely generated, and the complex need not be bounded.

## Not duplicates

No new nodes are proposed, hence no new/existing-node pairs require a same-tag distinction. Whole-DAG and blueprint searches for common quotient, quotient reduction, restriction scalars, and quotient tensor were performed. Existing `lem-weil-pbc-flat-scalar-restriction-kflat` is used rather than recreated. `lem-weil-pbc-ringed-common-quotient-pullback-comparison` includes geometric inverse image and composition coherences and is not used to hide this item's argument. `lem-weil-pbc-flat-restriction-ordinary-comparisons` is about normalized ringed-diagram inverse/direct images, not this quotient comparison; it is not cited.

## Review by Q16

I read `GOAL.md`, the stage-1 brief and stage document, the three blueprint levels in SETUP, the item's chapter and unit, and delivery-errors B through E (including the repeated new-target section). I read the current main-20261015 ancestor `def-weil-pbc-completed-pullback` (order 1329), and the ancestor's live statement and blueprint update. Its finite-evaluation and completion-map assertions need exactly the finite coefficient comparison, transitions and quotient units proved here. This is work below that unit route, not a replacement of it. The item is not the unit's key node, so no unit record changes are needed.

For the source I opened `proetale.tex`, Tag 099L, label `section-derived-completion-noetherian`, whose opening paragraph identifies the flat coefficient algebra and its quotients. I also read `sites-cohomology.tex`, Tag 06YS, label `lemma-K-flat-resolution`, its proof and the following 06YT quasi-isomorphism lemma, and Tag 06YY, label `lemma-derived-base-change`, including its resolving-class construction. I read `sites-modules.tex`, Tag 03EK, label `section-tensor-product`, with its sheafification definition and ordinary tensor formulas, and the tensor/restriction adjunction. I matched the tag-to-label assignments in `tags/tags`. There are no new-node sources to audit.

Step 1 cites `lem-pc-kflat-resolution`, whose statement explicitly supplies a K-flat resolution with flat terms on any ringed site, and `lem-weil-pbc-flat-scalar-restriction-kflat`, whose statement explicitly preserves both properties under the given flat map. I opened both statements. The exactness of restriction used here follows directly from `def-pc-sheaf-restrict-scalars` (same underlying abelian sheaves) and `def-weil-sheaf-of-modules-category` (sectionwise kernels and sheafified cokernels). The source and target rings and the small-site hypothesis are exactly those of the item.

Step 2 uses the actual sheaf tensor and module sheafification definitions, not ordinary objectwise tensors mislabeled as sheaves. I read `def-pur-sheaf-tensor-product`, `def-weil-presheaf-modules-sheafification` and `def-weil-sheaf-of-modules-category`. Their stated universal properties and cokernel description justify the two explicit maps. Balancing checks independence of the ideal representative, and the two displayed composites are identities. This is an elementary quotient-universal-property calculation, so I did not create another lemma node for it.

Step 3 writes out both inclusions $(J_nB)F=J_nF$, then the common-quotient comparison and its inverse. The equality uses that F is a B-module, not surjectivity of R to B. The supplied isomorphism is induced by the ring map, which is essential for matching the two S_n-actions. The cited `def-weil-pbc-ringed-tensor-section-calculus` states that pure sections determine linear maps; it is used only for that statement. The two formulas are proved in the step itself.

Step 4 cites `def-pc-tensor-complex-sheaves` for the actual differential when the second tensor factor is in degree zero, and the section-calculus statement for equality of sheaf maps. It explicitly checks the differential and arbitrary B-linear chain-map squares on $p\otimes s$. No claim that arbitrary derived morphisms are chain maps is made here.

Step 5 cites `def-weil-inverse-system`, whose statement defines tower morphisms by the adjacent transition equations, and the section calculus for equality of the maps being computed. Both routes around the adjacent square are written as $p\otimes t_n(s)$; the cone equality is written as $c_n(p\otimes1)=p\otimes1$. This verifies strict equality before localization and provides the whole cone from a constant tower, not unrelated derived-category component maps.

Step 6 cites `lem-pur-derived-change-of-rings`, which explicitly states quasi-isomorphism invariance on K-flat complexes, K-flat computation of the scalar-extension functor, and canonical compatibility of different resolutions. I also opened `lem-pur-left-derived-from-kflat-class`; it states the universal derived-functor construction for a resolving class and the computation on that class. The required class has resolutions by step 1; both tensor functors invert quasi-isomorphisms on it by flat scalar restriction and change of rings. The ordinary natural comparison and its inverse therefore descend via the universal property. This supplies naturality for derived morphisms, in addition to the already established strict assertion for a fixed representative. Off-unit uses of these general tools and the resolution theorem are declared in `split_report.tool_uses`, for the maintainer to judge.

I checked the small cases: M=0; J_n=R giving zero quotients; J_n=0 (then the assumed common quotient forces R to B to be an isomorphism); repeated ideals (identity transitions); the identity ring map; arbitrary unbounded P; and R=Z, B=Z_p with J_n=(p^n) on the point site. In the last case the comparison is exactly reduction to P/p^nP, with its ordinary units. Nothing in the formulas requires principal ideals or a point site. The construction also applies on the empty site. These checks found no statement dispute.

Every step's citation was checked against its statement, and `citations.json` copies those statements verbatim. All non-elementary inputs are named; no new node restates an item clause. Steps 2 through 5 are explicitly proved elementary calculations. Every step is shorter than 2000 characters, and no step hides a non-elementary comparison. The whole proof is marked agent-written to make its relation to the source honest. There are no SGA references.

## Unfinished work

None in the requested one-level split. The existing cited unsplit tools remain their own DAG items; they are neither silently proved nor altered here.
