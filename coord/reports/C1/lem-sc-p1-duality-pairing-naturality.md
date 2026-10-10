# Stage 1 report

1. Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-duality-pairing-naturality.json`: item, statement split.
- `dag/nodes/sec-picard-framework/lem-sc-p1-boundary-extension-composition.json`: statement-only generic homological fact, no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-p1-ext-yoneda-associativity.json`: statement-only generic homological fact, no Mathlib match.
- `dag/nodes/sec-picard-framework/def-sc-sheaf-cohomology-functor.json`: statement-only functoriality fact, no Mathlib match.

2. Attachments: none.

3. WANTED: `literature/stacks-project/derived.tex`, Tags 015M and the associated short-exact-sequence connecting-morphism discussion, for the two generic homological nodes.

4. The returned version was rejected because three support nodes merely restated the item's naturality and square clauses. I deleted those nodes. The revised proof writes the alpha calculation explicitly, writes the beta calculation using pullback and associativity, and proves the square by identifying $s$ with $\mathcal O_X\to\mathcal C$, introducing the extension class $\delta$, and showing both sides are $t(\varphi[1]\circ\delta\circ s)$. The sign convention is the standard sign-$+1$ convention for the cohomology boundary and Ext pushout boundary.

## Review by C1

I reread the item's statement, its parent blueprint Step 2, and the statements of `def-sc-ext-sheaf` and `lem-sc-ext-locally-free`. Those definitions provide the Ext groups and the identification used to type $\beta$. I also searched the whole DAG and blueprint before creating the three replacement nodes; no existing node states either generic compatibility fact. Their statements are strictly smaller than the item and introduce all ringed-space, module, extension, and composition data themselves. Each records searches by LeanSearch, Loogle, and Mathlib grep, all with no exact match.

Step 1 uses only the two existing definition/identification statements, and I verified each says exactly what the typing argument takes. Step 2 cites the new cohomology-functor statement, which explicitly gives $H^1(\varphi\circ u)=H^1(\varphi)\circ H^1(u)$. Step 3 uses the replacement Yoneda node, whose statement explicitly includes pullback as composition and associativity, so the cited statement supports both equalities. Step 4 uses the replacement boundary node for $\partial_Hs=\delta\circ s$ and the replacement Yoneda node for $\partial_E\varphi=\varphi[1]\circ\delta$ and associativity; both cited statements contain those formulas verbatim. I checked zero morphisms, zero sections, and split short exact sequences: every displayed identity reduces to $0=0$, and the sign is unchanged.

The prior report's mention of a separate `citations.json` was removed; citations are now represented by the item's actual `uses` and the three replacement node statements.
