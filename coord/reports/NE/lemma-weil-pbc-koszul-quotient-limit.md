# Stage-1 worker report

1. Files written: `dag/nodes/sec-proper-base-change/lemma-weil-pbc-koszul-quotient-limit.json` (statement, split); no new node files; `citations.json`.
2. Attachments: the existing declarations `lem-weil-pbc-noetherian-koszul-augmentation-pro-zero`, `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, and `lem-weil-pbc-filtered-category-directed-cofinal` are reused as DAG statements; no Lean declaration attachment was found for the item.
3. WANTED: none.
4. No source statement error was found. The imported proof had both paragraphs marked unsplit with no dependencies. I expanded them into two complete steps, cited the existing Koszul pro-zero and derived-limit/cofinality statements, and wrote the multinomial inclusions and common-augmentation compatibility explicitly. No duplicate node was created.
5. Nothing remains unfinished.

## Review by NE

I read the item blueprint proof and the full statements of `lem-weil-pbc-noetherian-koszul-augmentation-pro-zero`, `lem-weil-pbc-ringed-strict-tower-homotopy-limit`, and `lem-weil-pbc-filtered-category-directed-cofinal`. Step 1 instantiates the first statement with $A=\Lambda$ and $a_j=f_j$; its hypotheses give a Noetherian ring and finite generator list, and its conclusion is exactly that the augmentation-cone tower is pro-zero. I checked that its statement includes the quotient augmentation and the mapping-cone transition, so the step does not use hidden proof data.

For step 2 I checked the two ideal inclusions directly: a degree $r(m-1)+1$ monomial in $f_1,\ldots,f_r$ has an exponent at least $m$, while every $f_j^m$ lies in $I^m$. Thus the two quotient towers are cofinal. The directed-cofinal node explicitly states preservation of inverse limits under such reindexing. The strict-tower node explicitly states that a strict map whose mapping-cone tower is pro-zero induces an isomorphism on derived limits; derived tensor preserves the zero transition maps, so it applies after tensoring with $K$. Finally, all arrows in the triangle are induced by the same augmentation chain, which gives the displayed unit equation.

I tested edge cases in the statements: for $r=0$, the existing Koszul node's proof handles $I=0$ and the augmentation cone is acyclic; for $r=1$, the inclusions reduce to $I^m=J_m$; and for $m=a$ the quotient transition is the identity. The coefficient object $K$ is only tensor-translated and no flatness or regular-sequence hypothesis was added. The Mathlib searches for the item were run with LeanFinder, Loogle, grep, and LeanSearch; no Mathlib declaration states the required derived Koszul/quotient comparison.

## Statement corrected

STATEMENT-DISPUTED: the imported functorial-isomorphism assertion uses a definition of adic limit that explicitly specifies no morphisms between chosen triangles. Its functoriality is therefore not typed by that definition. The repair selects the total derived inverse-limit functor on strict towers, whose triangle realizes the existing adic-limit property, and uses its induced units. This makes the blueprint intent precise without imposing a new hypothesis on X, Lambda, I or K or weakening the isomorphism or unit equation. The completion-map definition has the same unspecified-lift issue for arbitrary chosen triangles; this item explicitly specifies its strict-tower interpretation and does not edit that dependency.

Old statement:

There is a functorial isomorphism

$$
c_K:K^{\wedge,\mathrm{Kos}}\xrightarrow{\sim}
R\varprojlim_nK_n
$$

such that $c_K\kappa_K=\operatorname{comp}_K$.

## Source error

The blueprint says the cone of Q_m to Lambda/J_m is tau_<0 Q_m. In the cohomological cone convention it is (tau_<0 Q_m)[1], not tau_<0 Q_m: take Lambda=F_p and the single generator f=0, m=1; Q=[Lambda --0--> Lambda] has negative truncation in degree -1, while the augmentation cone has its nonzero cohomology in degree -2. This shift does not affect pro-zero. The repair uses the actual mapping-cone statement of the existing node instead of repeating this error.

## Second reading by NE

- Original step 1, checked against lem-weil-pbc-noetherian-koszul-augmentation-pro-zero and Stacks 0921/0922: FAIL, the node states augmentation to Lambda/I^m, not Lambda/J_m, and the step invoked its proof. Replaced by direct statement specialization.
- Original step 2, checked against lem-weil-pbc-filtered-category-directed-cofinal, lem-weil-pbc-ringed-strict-tower-homotopy-limit, and Stacks 0H9L/0941: FAIL, the cofinal node only supplies existence of a particular directed presentation and preservation of ordinary limits; it does not apply to these specified quotient towers or give derived-limit invariance. Removed that citation and the unnecessary intermediate tower.
- Repaired step 1, checked against the complete existing Noetherian Koszul augmentation statement and 0921/0922: PASS, A=Lambda, finite list f_j, quotients I^m and strict transitions exactly match; no regular-sequence hypothesis.
- Repaired step 2, checked against the complete sheafification-exact and module-sheafification-interface statements: PASS, arbitrary site and constant presheaf ring are allowed; exactness gives a derived functor preserving the specified zero morphisms, with the cone formula written out.
- Repaired step 3, checked against lem-pc-kflat-resolution and def-weil-derived-tensor: PASS, one K-flat model gives strict comparison squares; tensor-cone sign and descent through quasi-isomorphisms are explicit, so zero morphisms remain zero after tensoring even for unbounded K.
- Repaired step 4, checked against the full strict-tower homotopy-limit statement, Stacks 0941, and the degree-zero augmentations: PASS, the cone hypothesis is supplied by step 3, naturality uses the strict derived functor, and the exact equality of strict unit maps yields the unit equation. Stacks 0H9L only promises a noncanonical isomorphism for arbitrary chosen triangles and is not used for naturality.
- New nodes: none; B1-B7 and duplicate/Mathlib-leaf audits have no new node to check. Every citation was regenerated as the full verbatim statement of the cited node. The item and source-checkout searches found no Koszul quotient-limit declaration to attach.
- Edge cases: K=0 and empty X give zero towers; r=0 gives I=0 and Q_m=P_m=Lambda with identity comparisons; for a field and I=0 the comparison is identity on the limit, and for I=Lambda the quotient tower is zero and the Koszul cone statement still applies; r=1 needs no cofinal reindexing. All indices are m>=1 and no unsupported level m=0 is used.

Changes: repaired the statement interpretation and documented its type failure; used the direct I-power cone node; removed the ordinary-cofinality citation and hidden proof citation; expanded constant sheafification, tensor-cone compatibility and strict unit equality; corrected source document locations; removed worker-written split_report.tool_uses (generic tool use is reported here for the maintainer, not authorized by the worker). The strict-tower homotopy-limit lemma is a generic ringed-site tool because the unit has no narrower limit-comparison statement. The sheafification and K-flat lemmas provide generic constructions on the same arbitrary ringed site.

Final step-4 naturality check: read lem-pur-derived-change-of-rings clause (2), which explicitly supplies the quotient functor and canonical resolution comparisons, and expanded the finite-degree filtration argument for Q_m. This avoids asserting functoriality merely from objectwise tensor models. Independent Mathlib grep with Koszul|koszul|homotopyLimit|homotopy_limit returned three incidental mentions (connections, a TODO, and introductory local-cohomology text), no matching declaration; actual results are in searches.jsonl and the item search record.

The second dry run flagged the added change-of-rings citation as outside the unit route. Repaired it using the unit own lem-weil-pbc-ringed-topoi-derived-tensor-pullback, whose full statement was read: identity topos morphism and Lambda_X to (P_m)_X give exactly the total left derived quotient-tensor functors computed by K-flat resolutions. Quotient transition naturality is now the explicit square of ordinary tensor maps before localization. The added outside-unit citation was removed; no tool-use override was written. This supersedes the preceding final-check citation, while retaining its explicit Koszul finite-filtration argument.
