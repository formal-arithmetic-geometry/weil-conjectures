## Worker report

Files written: dag/nodes/sec-smooth-purity/lem-cbc-abelian-comparison-injective-acyclicity.json (item, split); dag/nodes/sec-smooth-purity/lem-cbc-abelian-affine-comparison-vanishing.json (statement, unsplit, no Mathlib match); citations.json (verbatim statements supporting every step).

Attachments: none. The candidate AlgebraicGeometry.ProEtale.rightAcyclic_comparisonUpperStar_obj_of_injective in WeilConjectures/SixFunctors/ProEtale/Comparison/LowerStarAcyclic.lean:107–110 has a sorry. Searches of WeilConjectures by blueprint id and comparison/injective/affine concepts found no finished declaration for the item or the new affine fact. The existing etale restriction theorem is cited through its existing node, not recreated.

WANTED: none.

The imported item has no statement error. It has arbitrary abelian coefficients; the existing 099U node is about etale module sheaves in the finite-ring framework and cannot be used by identifying those coefficient categories. I retained the statement and supplied its previously empty proof. No Lean, compiler, Lake, or live project writes were used. The only unfinished mathematics is the new affine input, which is a strictly smaller theorem than global higher-direct-image vanishing and is deliberately statement-only. Its subsequent split should follow the two finite-cover approximations and Cech criterion in 099U, not invoke the item or the parent comparison theorem.

## New nodes

lem-cbc-abelian-affine-comparison-vanishing: arbitrary injective abelian sheaves over affine schemes; Stacks 099U, lemma-affine-vanishing. All Mathlib searches were run through msearch.py; both semantic phrasings return cotangent-complex and K-injective facts, not this result. Loogle and source grep give no match; LeanSearch is unavailable (HTTP Internal Server Error). No Mathlib leaves.

## Not duplicates

lem-cbc-abelian-affine-comparison-vanishing vs lem-weil-pbc-comparison-injective-acyclicity: the existing node assumes an affine base and injectivity in finite-ring etale module sheaves and concludes basis-object derived evaluation vanishing. The new node uses injectivity in arbitrary abelian etale sheaves and concludes global positive pro-etale cohomology vanishing on an affine scheme; its coefficients need not be torsion or carry an allowed finite-ring action.

lem-cbc-abelian-affine-comparison-vanishing vs lem-cbc-abelian-comparison-injective-acyclicity: the item is higher comparison direct-image vanishing on every scheme; the new node is global sections cohomology on an affine scheme. The proof must also identify restriction coefficients, preserve etale injectivity, and sheafify local vanishing; none of these conclusions are built into the new node.

DAG tag search for 099U/099V, keyword searches for affine/injective/cohomology and the complete blueprint searches '099U', 'affine vanishing', 'affine injective', 'injective abelian', and 'pro-etale cohomology' were read. The only relevant existing affine vanishing is the differently scoped finite-ring node above. Generic site higher direct images and localization already have nodes and were reused.

## Review by NU

I read proetale.tex, Tag 099V (lemma-relative-comparison), first proof paragraph, and the full statement and proof of Tag 099U (lemma-affine-vanishing). The latter requires only affineness and injectivity of an abelian etale sheaf, not Noetherianity, a finite ring, or torsion. Those are exactly the new node's hypotheses. Its definition dependencies introduce the scheme, sites, comparison, abelian cohomology and injectivity; there is no proof sketch in its statement. Its data has no Lean construction or hollow definition.

Step 1 uses the statement of lem-weil-pbc-site-higher-direct-image-sheafified-presheaf, read together with sites-cohomology.tex Tag 072W, lemma-higher-direct-images. It says the sheafification of derived object evaluation, not that ordinary sections of a higher direct image equal cohomology. The comparison definition explicitly gives the continuous inclusion and its direct image. This validates the application with q>0 and M on the source pro-etale site.

Step 2 uses precisely the abelian restriction statement of lem-sbc-etale-abelian-restriction-injectives. I read its statement and the source injective_upperStar_obj_of_etale_addCommGrp in TorsionAcyclic.lean:45–74: its coefficient category is AddCommGrpCat. U is etale over X, so its hypothesis applies without needing affineness or finite coefficients. This avoids invoking the module restriction theorem without a coefficient equivalence.

Step 3 uses clause (1) of lem-weil-proetale-weakly-etale-localization only for the equivalence of sites; it takes no module injectivity from that node. I read its statement, which explicitly identifies coverings and sheaf categories. I then read the complete statements of lem-cbc-comparison-pullback-sections and lem-weil-pbc-sets-etale-inverse-image-composition-units. The first includes both the actual section formula and its restriction maps, and the second includes coefficient naturality, units and associativity. Together they identify the two restricted comparison sheaves at every T and commute with each arrow T'→T. Naturality with addition/zero/negation and the underlying-set convention in def-weil-pbc-sites-and-cohomology make this an abelian sheaf isomorphism. This is an explicit elementary specialization of those statements, with no claim that geometric points detect pro-etale sheaves.

Step 4 cites the exact abelian localization theorem lem-weil-pbc-cohomology-over-object-localization, whose statement preserves injectives and identifies the derived evaluation with slice global sections. With step 3 this gives the group to which 099U applies: U affine, J injective abelian, q positive. It does not require X affine. The new affine theorem is not the item's conclusion rephrased: direct-image sheafification and all restriction identifications remain in the item.

Step 5 uses the affine open cover statement lem-pc-fppf-affine-open-cover (no quasi-compactness), open immersions being etale from lem-weil-pbc-open-immersion-etale, and the explicit composition property in lem-weil-pbc-etale-inverse-image-restriction. The site definition makes these jointly surjective families covers. I wrote the elementary sheafification argument from the universal property rather than citing an unrecorded local vanishing theorem: any map P→H is zero by separatedness on the affine cover, and uniqueness of factorization forces id=0 on P#. Thus no assertion of surjectivity of the sheafification unit on sections is hidden here.

I checked zero coefficients, the empty scheme and empty object, unrestricted positive q, non-affine and non-quasi-compact X, and injective sheaves with non-torsion sections. Vanishing is asserted only in positive degree; the proof does not incorrectly kill H^0. No geometric-stalk conservativity, finite coefficient ring or separatedness assumption is used. The unit sk-prop-sf-comparison has no proof steps; these steps realize the cohomology input to its ancestor's Step 4 and keep its route. Generic tools from other units are declared in split_report.tool_uses for maintainer review, without setting the maintainer tool_uses field. I corrected no statement; the main correction to the empty imported proof is to distinguish abelian injectivity from module injectivity and to spell out coefficient compatibility and sheafification.

## Second reading by NU

- Item statement: checked against Stacks Tag 099V (`lemma-relative-comparison`) and the blueprint ancestor; arbitrary schemes and injective abelian sheaves are retained, with only positive-degree acyclicity.
- New node `lem-cbc-abelian-affine-comparison-vanishing`: checked against Stacks Tag 099U (`lemma-affine-vanishing`); affineness and arbitrary abelian injectivity match, and no torsion, Noetherian, finite-ring, or dimension hypothesis was added.
- Step 1: checked Tag 099V against `lem-weil-pbc-site-higher-direct-image-sheafified-presheaf`; the sheafification of objectwise cohomology is used exactly as stated.
- Step 2: checked the restriction claim against `lem-sbc-etale-abelian-restriction-injectives` and its source declaration; coefficients are ordinary abelian sheaves, not finite-ring modules.
- Step 3: checked localization and coefficient identifications against `lem-weil-proetale-weakly-etale-localization`, `lem-cbc-comparison-pullback-sections`, and `lem-weil-pbc-sets-etale-inverse-image-composition-units`; the revised text explicitly derives additivity, zero, and negation from naturality.
- Step 4: checked slice cohomology against `lem-weil-pbc-cohomology-over-object-localization`; its hypotheses supply the affine input without assuming that X is affine.
- Step 5: checked affine covers, étale open immersions, and sheafification against the cited nodes and the sheaf axiom; the revised text explicitly handles the empty object through zero sections in an injective resolution.
- Existing-node audit: searched the DAG for 099U/099V and affine/injective/pro-etale variants; only the finite-ring module node exists and it is not a duplicate. Blueprint searches for the same concepts returned no node.
- Mathlib audit: ran independent LeanFinder, Loogle, and Mathlib grep searches; all produced no exact comparison-acyclicity theorem. Their actual results were appended to the affine node's search records.
- Source edge cases checked: zero coefficient, empty scheme/object, q=0 versus q>0, non-affine X, non-quasi-compact X, and non-torsion injective coefficients.
- Changes made: clarified that composition isomorphisms are additive by naturality with product, zero, and negation maps; clarified empty-object derived evaluation; recorded three additional executed Mathlib searches. No statements or citations were weakened or changed.
