# Stage-1 report: lem-sfb-space-affine-limits-schematic-stages

## Files written

All five node files are under dag/nodes/sec-six-functors-basics/ in this sandbox.

- lem-sfb-space-affine-limits-schematic-stages.json: item, statement, split into ten proof steps; statement unchanged.
- lem-sfb-space-affine-locality.json: statement-only general affine calculus, etale locality, representability over schemes and qcqs source permanence; Mathlib no match.
- lem-sfb-space-limit-sections.json: statement-only continuity of global functions on qcqs algebraic spaces; Mathlib no match.
- lem-sfb-space-limit-open-cover-descent.json: statement-only finite quasi-compact open-cover descent, including actual covering at the chosen stage; Mathlib no match.
- lem-sfb-space-limit-representable-isomorphism.json: statement-only representable isomorphism descent with the 084S hypotheses; Mathlib no match.

citations.json has 33 entries, one for every step/node pair, checked as literal substrings of the corresponding statements. searches.jsonl and the four *.search-results.json files retain actual search records and outputs. No Lean was written or compiled. No agents were started.

## Attachments

None. Searched lean/WeilConjectures for the item's tag and for schematicity, algebraic-space limits and the new node names; no declaration states this item. Scheme-only Mathlib declarations are not attachments.

## WANTED

None. Sources used are present in literature/stacks-project/.

## Corrections and scope

The item's statement is unchanged. The imported item had no proof. The related lem-sfb-affine-space-limit-schematic-stage is already split but cites this item, so using it would create a cycle. Its scheme-limit conclusion also would not provide the initial construction or affine projections. I did not use it.

The proof of 07SR tacitly passes from descended opens to a cover at a finite stage. I made this condition explicit in the open-cover supporting lemma. It follows after the individual 0827 descents by pulling back to one affine chart and applying scheme finite-cover descent (equivalently, eventual emptiness of the closed complement). This fills an omitted justification, not a change of source statement.

The proof of 07SQ uses a square-Jacobian model of the etale chart. I use the already existing general etale-algebra filtered-colimit descent node for the same finite etale model. The source remains the global-functions/etale-chart/Cartesian-square proof, followed by affine descent; no alternate unit route is introduced. The chosen algebra model is only auxiliary proof data. New nodes do not assert eventual schematicity or eventual affineness.

The blueprint ancestor utility returns None for this inherited chain, as already recorded by the item. I retained that value and its precise inherited place, and prepended this item in the new nodes' via lists. I read the latest blueprint unit, its DAG unit and the chapter record. This supporting item is not the unit's key statement, so no realization record is changed. Existing cross-unit scheme-limit, atlas, quotient and scheme-representability facts are generic tools; the requests are in split_report.tool_uses, not the maintainer-owned tool_uses field.

## Search results and small cases

Each new node has two actual LeanFinder phrasings, Loogle, Mathlib grep through msearch.py, and LeanSearch. All services answered. The hits include Scheme.exists_isAffine_of_isLimit (AffineTransitionLimit.lean:1040), nonempty_isColimit_Γ_mapCocone (same file:961), Scheme.exists_isOpenCover_and_isAffine and scheme morphism locality/descent. I read these hits and the relevant source types: their objects are Scheme, not arbitrary algebraic spaces. Abstract category descent does not construct the space or supply its etale presentation. No new node is a Mathlib leaf. The inherited item's five searches were retained; I also ran an additional semantic and grep check for the item itself, whose results again concern schemes.

I tested a singleton index, constant systems, the empty limit, empty finite covering, zero rings, and non-surjective transition maps. No proof assumes surjectivity of a transition or a projection. A directed tail is cofinal even without a least element. When the limit is empty, the affine chart argument still uses the zero ring and permits zero generators; the open-cover lemma explicitly allows n=0 and yields an empty stage. Quasi-separatedness is kept in every continuity/descent statement: it is needed for qc overlaps and must not be dropped. No affine-intersection assumption is made for merely quasi-separated schemes. The finite-etale model and its morphism are used with their specified isomorphism, not an arbitrary replacement object.

## Not duplicates

lem-sfb-space-affine-locality vs lem-trf-space-qc-separated-etale-local: the existing node tests quasi-compactness and separation; it does not give affine representability, affine composition, or qcqs source permanence.
lem-sfb-space-affine-locality vs lem-trf-space-separated-affine-chart-overlap: the existing node describes overlaps of charts of a separated space over an affine base; it is not the general affine morphism calculus and makes an extra separated-base hypothesis.
lem-sfb-space-affine-locality vs lem-pc-quasi-compact-local-on-target: the existing statement is Zariski locality of quasi-compactness for schemes, not affine morphisms of spaces or qcqs source permanence.
lem-sfb-space-affine-locality vs lem-sfb-representable-stack-fppf-locality: that node assumes stacks over a field; it does not state the arbitrary-scheme-base affine representability and qcqs source consequences needed here.
lem-sfb-space-affine-locality vs lem-sfb-space-four-property-fppf-descent: that node supplies fppf locality and base change for four properties. It does not assert affine composition, schematic source over a scheme target, or qcqs source permanence. The new general affine calculus includes those representability and permanence conclusions used before the qcqs hypotheses enter the main proof; it is not an additional eventual-limit lemma.
lem-sfb-space-limit-sections vs lem-sfb-affine-space-limit-schematic-stage: 084R is shared setup only; one states continuity of global functions, the other eventual schematicity.
lem-sfb-space-limit-sections vs lem-sfb-space-affine-limits-schematic-stages: 084R is shared setup only; the new node assumes an algebraic-space limit already exists and states a ring colimit theorem, neither existence nor eventual schematicity/affineness.
lem-sfb-space-limit-open-cover-descent vs lem-sfb-affine-space-limit-schematic-stage: sharing 07SR reflects the proof's use of open descent; the new node descends finite qc open covers without any schematicity assumption or conclusion.
lem-sfb-space-limit-open-cover-descent vs lem-sfb-space-affine-limits-schematic-stages: open-cover descent is an input to the finite-affine-cover argument, not a restatement of eventual scheme or affine stages.
lem-sfb-space-limit-representable-isomorphism vs lem-sfb-affine-space-limit-schematic-stage: 084R is setup; the new node concerns a fixed lfp morphism between two representable objects, not whether the bases are schemes.
lem-sfb-space-limit-representable-isomorphism vs lem-sfb-space-affine-limits-schematic-stages: the former assumes an existing space limit and detects a fixed morphism's isomorphism, while the item constructs the limit and descends affineness/schematicity.

I searched all DAG sources for 07SI, 0827, 084S, 03WG, 03WH, 03WI, 03KG, 03KM and the corresponding keywords. The blueprint search by those tags and phrases did not find the new statements. Scheme sections and scheme open-cover nodes are restricted to schemes, so cannot replace their space counterparts before a schematic stage is obtained.

## Review by Q108

I read spaces-limits.tex at 07SF, 07SQ and 07SR and Situation 084R. For the new nodes I read 07SI, 0827, 084S and the finite-open-cover omission of 07SR, together with 086W for eventual emptiness; for affine calculus I read spaces-morphisms.tex 03WG/03WH/03WI and the quasi-compact/separated target tests 03KG/03KM. The qcqs consequence is composition of quasi-compact maps and separated-over-quasi-separated; this is generic affine permanence, not a limit theorem. I also read the algebra.tex 00U2(9) etale model statement, morphisms.tex 01TQ for finite presentations on arbitrary affine opens, limits.tex 01YX/01YW and 07RR, spaces-properties.tex 03FV and the affine-target construction 05Z1, and schemes.tex 01JJ.

Step 1 uses the actual scheme-limit existence theorem, the space fibre-product theorem, etale base change from chartwise permanence, and affine base change/representability. I checked that no qcqs assumption is required for this construction. R_0 is a scheme because the diagonal of an algebraic space is representable. The limit equivalence relation is checked on every test scheme with unique compatible witnesses.

Step 2 uses the full etale-relation quotient statement, including local lifts and R=U times_Q U. Its injectivity argument constructs compatible witnesses in R_i, rather than assuming that quotient commutes with inverse limit. Step 3 uses affine target locality on the single chosen atlas; the arbitrary W base-change identity is proved directly on test schemes and the tail cofinality is written out.

Step 4 uses the existing finite-affine-atlas statement, whose qc convention matches the item's, the new qcqs affine-source consequence, and the exact space and scheme global-function continuity statements. All U_i are affine, so their qcqs assumptions hold. In step 5 I checked the existing etale-algebra model theorem gives an A-algebra isomorphism as required. I corrected the initial draft to cite the real 01TQ affine-open finite-presentation lemma: the lfp definition alone would not justify finite presentation on the whole affine chart. The surjectivity theorem has qcqs schemes and a locally finitely presented map; each of its initial schemes here is affine, and etaleness provides lfp. Etale base change is an explicit cited permanence statement.

Step 6 is finite-data algebra: lift finitely many generators, then kill finitely many relations using eventual zero. The actual scheme affine-target bijection and sheaf descent give the canonical space-to-Spec map, with agreement on overlaps; this is the elementary atlas argument of 05Z1, not a new theorem whose proof is hidden. Step 7 uses the exact 084S representable-isomorphism statement. I checked both objects over Z_0 are representable, that T_0 is qcqs because it is affine over qcqs Z_0, and U_0 is affine. I corrected the first draft to cite the existing chartwise-etale permanence theorem for the map between the two etale objects, and the etale definition for lfp. At the limit the map is the specified B identification from step 6, so is an isomorphism with no choice ambiguity.

Step 8 uses the existing theorem that a map between affine schemes is affine and the new target-locality statement. The bottom cover is the surjective etale model from step 5, so descent applies. Step 9 uses the open-cover lemma with actual covering at a stage, applies the already-proved affine part to the open inverse systems, and takes a common upper bound for finitely many stages. It then applies the precise functorial scheme representability criterion: the fppf sheaf is a Zariski sheaf, its open subfunctors are represented, and they cover every test. Step 10 uses exactly the representability and affine-source consequences of affine permanence. These last two steps handle the empty cover explicitly.

Against delivery-errors B, every new statement introduces its objects, spells out qcqs/affine notions, gives tags and labels and carries no proof. Against C, I opened every cited node and compared the used conclusion, then checked each of the 33 quote entries; proof_deps is their union. Against D, the substantial quotient and finite-etale-chart arguments remain in the item and no new node states any eventual-scheme or eventual-affine clause. Against E, I checked all representability, qcqs, finite-presentation and base-change hypotheses described above and the edge cases. No non-elementary step is longer than 2000 characters. The independent server check_dag passed, and review_split reported PASS before the full delivery dry run.

## Unfinished

No part of the requested one-level split is left unfinished. The four supporting nodes intentionally remain statement-only for subsequent stage-1 work. Their future splits must prove their assertions; no Lean proof is claimed here.
