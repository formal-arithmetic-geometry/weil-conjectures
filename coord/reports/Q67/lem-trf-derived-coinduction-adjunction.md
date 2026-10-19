Files written:

- `dag/nodes/sec-trace-formula/lem-trf-derived-coinduction-adjunction.json` — item split into five proof steps; no new nodes and therefore no Mathlib leaves.
- `citations.json` — verbatim statement quotes for every cited node at every step.

Attachments: none.

WANTED: none.

The imported statement agrees with dualizing.tex, Tags 0A70 and 0A71. I found no source or DAG defect and did not change its hypotheses or conclusion. The existing `lem-trf-algebraic-shriek-derived-hom-adjunction` is a strictly smaller same-unit result giving the internal-Hom adjunction and evaluation formula; it is cited rather than duplicated. The one-object ringed-site specialization is explicit in the proof, so the generic sheaf-of-modules K-injective and derived-Hom nodes apply to ordinary module derived categories.

No part remains unfinished. I tested the construction on the identity map $R=B$ (coinduction is the identity and evaluation at $1$ is the identity), on $K=0$, and on a general underlying module map to check that restriction of scalars preserves and reflects isomorphisms. No new Mathlib search was needed because the item already has the required recorded LeanSearch, Loogle, LeanFinder and grep searches and its statement was unchanged.

## Review by Q67

I read the item node, the unit `sk-i-curve-zero`, the chapter `sec-trace-formula`, and the source passage `literature/stacks-project/dualizing.tex`, Tags 0A70 and 0A71 (including the K-injective model and evaluation-at-one counit). I also read each cited DAG node in full: `prop-pur-kinjective-resolutions-exist` supplies functorial K-injective resolutions; `def-pur-derived-internal-hom` defines the Hom-complex derived object and its choice-independent functorial construction; `lem-pur-rhom-well-defined` supplies quasi-isomorphism invariance; `lem-trf-algebraic-shriek-derived-hom-adjunction` states the ring-map coinduction internal-Hom adjunction with the exact evaluation-at-one formula; `lem-pur-rhom-global-sections` identifies $H^0$ of internal Hom with derived-category Hom; and `lem-weil-pbc-unbounded-derived-iso-cohomology` gives the all-degrees cohomology criterion for isomorphisms.

Step 1 uses exactly the K-injective existence, derived-Hom construction, and Hom-complex quasi-isomorphism invariance just listed, so it establishes both independence of representatives and functoriality. Step 2 checks the right-multiplication $B$-action directly from multiplication in $B$ and the degree-zero Hom differential, then uses the definition node for the underlying $R$-object. Step 3 specializes the existing ring-map adjunction node with $P=R$ and $A=B$, and uses the one-object case of the global-Hom node to pass from internal-Hom isomorphisms to the required Hom-set bijection. Step 4 takes the identity morphism under that bijection; the cited evaluation formula gives precisely $h\mapsto h(1)$, so the counit is normalized correctly. Step 5 checks the exact forgetful restriction on cohomology and applies the cited derived cohomology criterion to prove conservativity. I verified that every hypothesis is present at the step where it is used, that no step invokes a proof detail absent from its cited statement, and that the five-step proof follows the source route without restating the item as a new node.
