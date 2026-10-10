# Stage 1 report

## Files written

- `dag/nodes/sec-picard-framework/lem-sc-ext-stalk-localization.json`: statement, split proof, dependencies, blueprint and audit fields.
- `dag/nodes/sec-picard-framework/lem-sc-derived-internal-hom-stalk-localization.json`: statement-only coherent-sheaf specialization of 0GM8 and 08E8; no Mathlib match.
- `dag/nodes/sec-picard-framework/lem-sc-rhom-cohomology-ext-ring.json`: statement-only ring derived-Hom/Ext comparison from 0A64; no Mathlib match.

## Attachments

None. No sorry-free slopmaster2 declaration states this item.

## What was checked

I read the actual Stacks TeX in the local source checkout: `equiv.tex` Lemma `lemma-Ext-0-regular` (0FZ3), `cohomology.tex` Lemma `lemma-stalk-internal-hom` (0GM8) and Section `section-ext` (0BQP), `perfect.tex` Lemma `lemma-identify-pseudo-coherent-noetherian` (08E8), and `more-algebra.tex` Section `section-RHom`, equation `equation-h0-RHom` (0A64). The tag index confirms these labels. I also read the Picard unit and parent blueprint node. The imported item's statement is kept: it uses sheaf Ext defined via derived internal Hom with an injective resolution of the second argument.

The earlier delivery cited 08DJ for a derived Ext comparison, but 08DJ is a tensor-Hom adjunction and does not say that. It also treated pseudo-coherence of a coherent module and the ring derived-Hom/Ext comparison as elementary. The revised first node incorporates the Noetherian/coherent specialization supplied by 08E8, leaving no undefined pseudo-coherence or bounded-below notions in its statement. The second node states precisely the 0A64 comparison needed by step 3. No source is WANTED; the TeX was available in `/home/ubuntu/c1-stacks-review/` on this machine, although `literature/stacks-project/` is not populated in this clone.

## Review by M1

For the first new node, 0GM8 applies to a ringed space when its first complex is pseudo-coherent and its second is locally bounded below. Here a Noetherian scheme is a ringed space, 08E8 makes coherent F[0] pseudo-coherent, and G[0] is bounded below by inspection. Its statement defines the local-ring derived Hom through `def-pur-derived-internal-hom` on the one-point site, and cites the cohomology-sheaf and derived-category definitions. These are the exact hypotheses of item step 1; its only cited statement already says the resulting stalk isomorphism. At a one-point scheme this reduces to the identity comparison, and for F=O_X in degree zero it gives the expected local Hom comparison.

For the second new node, 0A64 says `H^n(RHom_R(L,M)) = Hom_{D(R)}(L,M[n])` for every integer n. Applying it to modules in degree zero and n>=0 gives the Ext group of `def-pc-ext`. The node introduces R, M, N and n, and defines its derived Hom through the one-point site; at n=0 it reduces to Hom_R(M,N), and for M=R higher degrees vanish. Step 3 cites exactly this comparison with R=O_{X,x}; the equality with the item's Ext follows from the quoted sentence. Step 2 cites the module-specialization sentence in `def-weil-pbc-sheaf-ext`, whose preceding display explicitly defines sheaf Ext as the cohomology sheaf of derived internal Hom. Substitution of the two identifications into step 1 is elementary.

I searched all DAG nodes and the whole blueprint by concept and source tag before adding the new ring node, and read the existing `lem-weil-pbc-ext-via-injective-resolution`: it computes Ext with an injective resolution but does not state a comparison with ring-valued derived internal Hom. The Lean source has no matching declaration or blueprint tag for the item or either new node. Mathlib's `Ext.homAddEquiv` and injective-resolution comparisons do not define ring-valued derived internal Hom, so neither new node is a Mathlib leaf. Both new nodes are statement-only, have self-contained objects and hypotheses, cite defining nodes for their notions, and carry the correct TeX labels. I checked every quote in `citations.json` against the statement it names and every item step against its source. The item's imported `source.place` still mentions 08DJ; that field is maintainer-owned for existing nodes in remote deliveries. Its editable proof steps and `proof_origin` now cite 08E8 and 0A64 instead.

## What could not be finished

No Lean compilation is part of stage 1.
