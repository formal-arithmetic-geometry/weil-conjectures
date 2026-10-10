# Delivery report

Files written:

- `dag/nodes/sec-picard-framework/lem-sc-p1-ext-yoneda-functoriality.json`: split item.
- `dag/nodes/sec-picard-framework/lem-sc-ext-yoneda-composition-derived.json`: statement-only supporting node; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-ext-locally-free-second-naturality.json`: statement-only supporting node; no Mathlib match.

Attachments: none.

WANTED: none.

The item had no Lean declaration and no matching blueprint node. The repository already contains `def-pc-ext`, which states the derived-category Ext functoriality, and `lem-sc-p1-ext-locally-free-naturality`, which is only naturality in the first locally free argument. I therefore created only the two missing smaller statements: the Yoneda/derived composition identification and naturality of the locally free Ext-cohomology comparison in the coefficient module. Both were searched for in the DAG, blueprint, source checkout, and Mathlib before creation.

## Review by K1

I read the item, its ancestor `thm-sc-p1-duality`, the neighboring associativity and locally-free naturality nodes, and the source labels for Stacks Tags 06XP, 06XR, 010I, and 01DZ. Step 1 cites `def-pc-ext` for exactly the precomposition and postcomposition formulas in its statement, while `lem-weil-pbc-ext-via-injective-resolution` supplies the corrected injective-resolution interpretation of the project’s Ext convention. Step 2 cites the new statement for the Yoneda product’s derived-category description and the existing associativity node only for the named Yoneda operation; its degree-zero specialization is explicit. Step 3 cites the new second-variable naturality statement, the existing `Ext^i(O_X,G)=H^i(X,G)` clause, and the cohomology-functor statement, which supplies the map `H^i(phi)`.

I checked hypotheses: all statements quantify the scheme, module objects, morphisms, and degree; the new naturality node assumes finite locally free first argument exactly as required by the existing comparison. Small cases checked were degree zero (ordinary Hom composition), identity morphisms, the zero morphism, and `F=O_X`, where the comparison is ordinary sheaf cohomology. Mathlib searches for each new node and the item included LeanSearch, Loogle, and source grep; only abstract Ext APIs matched. The blueprint fields, proof dependencies, citations, and tool-use declarations were checked against the route. No proof was moved wholesale into a new node, and no source or statement error was found.
