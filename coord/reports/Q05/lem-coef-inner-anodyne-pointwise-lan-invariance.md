Files written:

- `dag/nodes/sec-six-functors/lem-coef-inner-anodyne-pointwise-lan-invariance.json` — statement, three proof steps, one new statement-only node and seven existing dependencies.
- `citations.json` — nine verbatim step-to-node quotations.

Attachments: none.

WANTED: an archival copy of Kerodon Proposition 7.3.1.14 (02YL), Change of Diagram, including its proof.

What was checked and corrected: the imported node had the right statement but no proof. I checked the statement against Kerodon 02YL and verified the orientation of the slice $C_{/c}$ and the canonical legs. The Lean source under `/home/ubuntu/weil-src-slopmaster2/WeilConjectures` contains no declaration tagged `lem-coef-inner-anodyne-pointwise-lan-invariance`; the upstream master source is reference only and likewise has no finished declaration. I retained the existing Mathlib search records after reading their results: they find ordinary Kan-extension APIs but no quasicategorical inner-anodyne invariance.

## Not duplicates

lem-coef-inner-anodyne-slice-categorical-equivalence vs lem-coef-inner-anodyne-pointwise-lan-invariance: the new node proves only the categorical equivalence of the two slice indexing simplicial sets; the item additionally transfers the canonical pointwise cocone colimit property for every $c$.

lem-coef-inner-anodyne-slice-categorical-equivalence vs lem-coef-cartesian-base-equivalence-invariance: the existing node is a broad marked-model assertion whose dependency closure reaches this item through the unresolved pointwise mapping-property node; the new node is the independent slice-right-fibration statement used here and avoids that circular route.

## Review by Q05

I read the item node, `sk-prop-sf-biduality-general.json`, `sec-six-functors.json`, the ancestor blueprint node and its proof paragraph, and the full statements of every cited DAG node. I also read the new slice pullback node and its four recorded Mathlib searches. In Step 1, that node supplies the categorical equivalence $L_{/c}\to K_{/c}$, with its right-fibration and cartesian-lifting hypotheses checked and no quasicategory hypothesis on $L$ or $K$. In Step 2, the Joyal functor-equivalence test applies to this exact map and retains all transformations and higher simplices; the enhanced functor cone calculus supplies the induced equivalences on right-pinched mapping spaces. In Step 3, I applied the relative-cone constant-target criterion with base $D\to\Delta^0$ to the two canonical cocones. The restriction equivalence carries the diagram, canonical transformation, and fixed apex $F(c)$ exactly, so the criterion is true on $K_{/c}$ exactly when it is true on $L_{/c}$; quantifying over $c$ gives the stated iff. I checked $L=\varnothing$, $K=\varnothing$, $K=\Delta^0$, and $C=\Delta^0$: the slices and cocone criteria reduce to the expected initial-object and identity cases. Every citation quote is copied verbatim from its node statement, and every proof dependency is used. The new node is statement-only and strictly smaller than the item; its distinction from the broad existing cartesian-base node is recorded above. There is no cycle, off-unit tool, SGA source, statement correction, or long step.

What could not be finished: none.
