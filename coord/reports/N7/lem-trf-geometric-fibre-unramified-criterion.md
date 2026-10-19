1. Files written:

- `dag/nodes/sec-trace-formula/lem-trf-geometric-fibre-unramified-criterion.json` — statement, split proof, no Mathlib leaf.
- `dag/nodes/sec-trace-formula/lem-trf-unramified-field-fibre-decomposition.json` — statement-only Stacks lemma, no Mathlib match.
- `dag/nodes/sec-trace-formula/lem-trf-unramified-ordinary-fibre-criterion.json` — statement-only Stacks lemma, no Mathlib match.
- `citations.json` — verbatim statement excerpts for every proof citation.

2. Attachments: none.

3. WANTED: none.

4. What was checked and corrected:

The imported item statement was checked against Stacks Morphisms Tag 02G8 (the locally-finite-type ordinary-fibre criterion), Tag 02G7 (the field case), and Descent Tag 02VM. It is mathematically correct as stated: local finite type is the only finiteness assumption, geometric fibres may be empty, and the base may be non-quasi-compact or non-Noetherian. No Lean declaration in the reference source states the item.

The new field-fibre node records exactly Tag 02G7(1), including arbitrary disjoint unions and finite separable field extensions. The new ordinary-fibre node records exactly the implication 02G8(2), with the scheme-theoretic fibres and their residue fields introduced in the statement. I searched the whole DAG and blueprint for both facts; the existing affine product node is only an affine special case and does not replace the scheme-level statements.

## Review by N7

I read the item source and the three relevant Stacks proofs. In step 1, the cited base-change node explicitly says that arbitrary base changes of unramified morphisms are unramified, and the geometric-fibre definition identifies the displayed morphism as that base change. In step 2, I checked that the ordinary fibre is the scheme-theoretic fibre and that the geometric fibre is its base change along the algebraic-closure field extension; the field-extension node supplies an fpqc singleton covering, and the cited descent node states that unramifiedness descends from every member of an fpqc covering. Step 3 uses only the new field-fibre node's exact disjoint-union conclusion. Step 4 uses the locally-finite-type hypothesis and the new ordinary-fibre criterion, whose statement exactly supplies the Tag 02G8 implication. I verified all hypotheses, including the empty-fibre case, and tested the edge cases of an empty scheme and the identity morphism over a field. I corrected the imported blueprint location to identify the geometric-fibre assertion used by the nodal-family proof and recorded the three generic cross-unit facts as tool uses.

5. What I could not finish: nothing; no Lean code or compiler was used.

## Not duplicates

lem-trf-unramified-field-fibre-decomposition vs lem-trf-geometric-fibre-unramified-criterion: the new node is the field-base characterization for one morphism to Spec k; the item compares a morphism over an arbitrary base with all geometric fibres.
lem-trf-unramified-field-fibre-decomposition vs lem-weil-pbc-unramified-algebra-over-field-product: the existing node treats only affine Spec C and gives a finite product of fields; the new node treats arbitrary schemes over a field, including non-quasi-compact disjoint unions.
lem-trf-unramified-field-fibre-decomposition vs lem-weil-pbc-unramified-fibre-point-isolated: the existing node proves isolation of one point in a fibre under a pointwise hypothesis; the new node gives the full scheme-level decomposition and separability equivalence.
lem-trf-unramified-field-fibre-decomposition vs lem-weil-pbc-unramified-over-field-discrete: the existing node proves only that the underlying space is discrete in the forward direction; the new node also identifies every component as a finite separable field spectrum and includes the converse.
lem-trf-unramified-ordinary-fibre-criterion vs lem-trf-geometric-fibre-unramified-criterion: the new node is the ordinary scheme-theoretic-fibre implication used inside the proof; the item is the separate geometric-fibre iff criterion.
lem-trf-unramified-ordinary-fibre-criterion vs lem-sc-etale-evaluation-separable: the existing node concerns separability of residue evaluations for an etale morphism, while the new node concludes unramifiedness from all ordinary fibres.
lem-trf-unramified-ordinary-fibre-criterion vs lem-sc-etale-residue-field-map-etale-tool: the existing node proves a residue-field map is etale under an etale hypothesis, while the new node is the converse fibre criterion for arbitrary locally finite type morphisms.
lem-trf-unramified-ordinary-fibre-criterion vs lem-sc-etale-units-stalk-evaluation-overfield-bijective: the existing node is a stalk/evaluation bijection for etale units, while the new node is a global morphism criterion.
lem-trf-unramified-ordinary-fibre-criterion vs lem-sc-etale-units-stalk-evaluation-overfield: the existing node identifies stalk evaluations over a field, while the new node characterizes unramifiedness from every scheme-theoretic fibre.
lem-trf-unramified-ordinary-fibre-criterion vs lem-weil-pbc-etale-residue-field-extension-separable: the existing node derives separable residue extensions from etaleness, while the new node derives unramifiedness from fibre decompositions and assumes no flatness.
