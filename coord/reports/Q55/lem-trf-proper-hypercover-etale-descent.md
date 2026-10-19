# Stage-1 delivery: lem-trf-proper-hypercover-etale-descent

## Files written

All node files are under `dag/nodes/sec-trace-formula/`.

- `lem-trf-proper-hypercover-etale-descent.json`: item, split into nine proof steps; statement unchanged, no Mathlib match.
- `def-trf-ph-scheme-site.json`: definition, unsplit; no Mathlib ph topology match.
- `lem-trf-ph-etale-torsion-comparison.json`: statement, unsplit; no Mathlib match.
- `lem-trf-site-hypercover-derived-descent.json`: statement, unsplit; no Mathlib match.
- `lem-trf-simplicial-ph-etale-square.json`: statement, unsplit; no Mathlib match.
- `lem-trf-total-site-derived-components.json`: statement, unsplit; no Mathlib match.

`citations.json` contains a verbatim statement quote for every use in every numbered proof step. `searches.jsonl` is the unmodified msearch log; `search-results/` retains the returned signatures and descriptions. The scripts and search inputs are sandbox-only working material.

## Attachments

None. Searches for the item id and its `(blueprint: ...)` tag in the project source found no declaration. Concept searches under WeilConjectures found only 0/1-hypercover gluing, pro-object limit presentations, ordinary sheaf descent, and generic adjunction machinery, not proper hypercover cohomological descent. The new ph, total-site and full-hypercover inputs have no corresponding project declaration. No Lean was written or compiled.

## WANTED

None: all mathematical sources used are available in the shared literature tree.

## Audit and changes

The item was an unsplit statement with recorded searches and no proof. Its torsion-ring hypothesis, all matching-map hypotheses, ordinary unit normalization, arbitrary schemes, and quantification over every complex on every base change are retained verbatim. I read its chapter and unit records, its nearest blueprint ancestor in main-20261015, and the ancestry through Orgogozo's modification and nearby proper hyperdescent nodes. This split expands the first descent isomorphism of Orgogozo Lemma 3.1.1 already isolated by that ancestry; it does not replace the normal-cone route or change the unit record.

Stacks `spaces-simplicial.tex`, section-proper-hypercovering-spaces, explicitly permits replacing algebraic spaces by schemes and the ph comparison references by their scheme counterparts. I followed its 0DHL proof. The text of 0DHL says all D+ complexes, but the comparison it cites (0DE5 for schemes, 0DGU for spaces) has a torsion-cohomology hypothesis. I make no use of an unrestricted version: the present item already has a fixed torsion ring, and step 8 verifies torsion. No correction of this item's statement is needed. There is also an apparent label typo in 0DHL's proof, which names lemma-compare-simplicial-objects rather than the ph-etale comparison just invoked; the correct comparison is 0DHJ. The split names that square explicitly.

The new nodes are foundational inputs to the ph comparison argument, not clauses copied out of the item. The general site descent theorem assumes covering matching maps in one site; the item's proper matching maps are not etale covers, so applying it requires the ph site, two comparison morphisms, a total-site component argument and an explicit unit calculation. Conversely none of the new nodes alone asserts the item's conclusion.

I initially considered a sixth new node for constant coefficients on arbitrary topoi. On reading `lem-pur-ringed-coefficient-restriction-counit` and `lem-pe-constant-left-module-inverse-image`, I removed that uncommitted candidate: step 7 obtains the required unit identity directly by transposition of their statements. I also removed derived composition from the new total-component statement and instead cite the existing generic derived-adjunction normalization. These corrections avoid duplicating available general tools. The searches for the discarded candidate remain in the log but are not attributed to a delivered node.

The two geometric stability inputs that are not already closed, and the general homological tools from other units, are declared in `split_report.tool_uses`. These are tools for finite matching geometry and site-level coefficient/adjunction operations; they do not substitute another proof route for this unit.

## Searches and existing-node checks

Before creating nodes I searched all DAG files for ph topology, ph/etale comparison, cohomological descent, proper hypercover, the Stacks labels and tags 0DHL, 0DE5, 0DGU, 0D8N, 0D97, 0DHJ, 0D99, 09WG, 0DBQ, 0D6E and 0D6J. I ran blueprint_refs searches for `ph topology`, `cohomological descent`, `hypercover`, `simplicial site`, `derived direct image`, `forgetting coefficients` and `module coefficients`. The hypercover results are the split etale finite-hypercover cohomology nodes and pro-etale hypercover computations; none supplies descent on the big ph site. The existing simplicial spectral-sequence node concerns morphisms of simplicial schemes and their small etale topoi, so it does not cover the change-of-topology map from a big ph total site.

For each delivered node, and for the item, I ran msearch leanfinder with two distinct phrasings, leansearch, loogle and grep. All five searches per node returned successfully. The records reproduce their exact tool/query and log result, without replacing unavailable responses by absence claims. The hits are ordinary OneHypercover gluing, augmented simplicial and Cech objects, ordinary continuous sheaf pushforward and generic sheafification, and the standard Zariski/jointly-surjective/morphism-property scheme topologies. I read their returned signatures and the candidate OneHypercover source and small-site constructors: they do not state full derived hypercover descent, ph/etale comparison, or component derived images on a total site. In particular the proper-morphism family topology is not ph: its definition omits ordinary Zariski covers, which ph must contain. No hit provides an exact or one-line specialization for a delivered node.

## Not duplicates

lem-trf-simplicial-ph-etale-square vs lem-trf-simplicial-derived-image-spectral-sequence: the existing statement gives small-etale derived images and an augmentation spectral sequence for diagrams of schemes; the new statement constructs the comparison from the big ph total topos and its augmented square, without any spectral sequence assertion.

lem-trf-simplicial-ph-etale-square vs lem-trf-simplicial-proper-exchange: the existing statement compares a proper simplicial scheme with its base change inside etale topoi; the new statement changes topology from big ph to small etale and requires no properness or base-change diagram.

lem-trf-total-site-derived-components vs lem-trf-simplicial-derived-image-spectral-sequence: the existing statement only covers a morphism of simplicial schemes on small etale topoi; the new component formula applies to general simplicial sites, including the ph/etale comparison, and explicitly identifies the restricted unit. It has no spectral sequence or general derived-composition clause.

lem-trf-site-hypercover-derived-descent vs thm-weil-pbc-hypercover-cohomology: the existing statement computes individual sheaf cohomology by a filtered colimit over split finite etale hypercovers on qcqs schemes; the new theorem concerns the derived unit into the total topos of one full representable hypercover in any small site.

lem-trf-site-hypercover-derived-descent vs det-pe-hypercover-complex: the existing statement computes a pro-etale complex on affine weakly contractible hypercovers; the new theorem treats arbitrary site hypercovers and the sheaf-level augmentation unit.

## Review by Q55

I read the item against the scheme version of 0DHL with `spaces-simplicial.tex` open at the proper-hypercover section and its full proof. I read 0DE5 in `etale-cohomology.tex`, 0D8N and 0DHJ/0D97 in `spaces-simplicial.tex`, the ph definition and characterization 0DBC/0DBQ in `topologies.tex`, and the generic composition and coefficient-comparison constructions 0D6E/0D6J in `sites-cohomology.tex`. For the new ph definition I checked that its generators are the generators stated at the start of section-ph and in lemma-characterize-sheaf; it is not the h topology on unrestricted non-Noetherian schemes. The comparison node retains the torsion condition and imposes neither Noetherian nor prime-to-characteristic assumptions. The generic descent node is the bounded-below case of 0D8N, with finite matching limits stated explicitly, rather than a new claim about improper etale covers. The square is exactly the scheme version of 0DHJ, including the directions of its four morphisms. For the total-component node I checked the component restriction and K-injective argument of 0D97 and the exact-left-adjoint description behind 09WG. Its objects are sites and sheaves, not only schemes. All new nodes have statements only and no proof material hidden in the statements.

Step 1 uses the actual statements of proper base change and composition, closed-immersion base change and properness, and the diagonal definition in def-weil-proper-morphism. These statements supply precisely the operations in the written induction. The finite equalizer is given by its maps to the product, rather than an unexplained assertion that matching limits stay proper. Only lower-degree proper objects occur. The empty product is X; the n=0 case is assumed; no finite type of X over a field or separatedness of X is used. Closedness belongs to the relative diagonal of Q over X.

Step 2 uses the fibre-product universal property and the exact general proper/surjective base-change statements. I checked both hypotheses are applied to matching morphisms, not to a nonproper structure map or to an etale base change only. The test-object description proves the matching-object identification and compatibility of its matching map. It applies to arbitrary Y and includes M0=Y.

Step 3 uses the new ph definition and the full statement of general site hypercover descent. The former makes every proper-surjective matching singleton covering; the latter gives the derived unit for any bounded-below E. The slice at X/X is the original site, and the slices at U_n are the required big ph sites. The universe convention is explicit on both nodes; the scheme universe is enlarged before taking a small site presentation. There is no use of a small-index theorem on an unbounded class-sized category.

Step 4 uses the new square statement for its actual inverse-image comparison. It uses the geometric-morphism definition for exact inverse image on abelian objects: finite-limit preservation and preservation of colimits as a left adjoint give exactness, and multiplication maps remain multiplication maps. This preserves bounded-below and torsion cohomology. The square is available for every augmented simplicial scheme, without already assuming the conclusion of this item.

Step 5 uses exactly the unit isomorphism of the ph/etale comparison on each U_n and the restricted-unit formula of the new total-component theorem. Both statements explicitly say these are the ordinary units. The cone test is elementary because exact restriction computes each cohomology sheaf componentwise, and a sheaf family whose components vanish is zero. There is no unbounded spectral-sequence convergence assertion and no cartesianness assumption on an arbitrary total sheaf.

Step 6 uses the existing ring-sheaf Grothendieck theorem at the integer sheaf to meet every Grothendieck hypothesis in the derived composition normalization node. That node explicitly says the conjugate isomorphism identifies derived composite units and counits; the composite-adjunction definition gives the written formula. The square identifies the two factorizations. I checked the directions: Ra applied to eta_h follows eta_a, and Rh_X applied to eta_b follows eta_h_X. The left factor is invertible from step 5, and both right factors from step 3 and the comparison on X. Thus it proves invertibility of the specific eta_a, not just existence of an isomorphism of its endpoints.

Step 7 uses the statements of the existing arbitrary-site constant inverse-image theorem and the arbitrary-topos coefficient-restriction counit theorem, not a scheme-only specialization. Set A=Z and R_X,R_Y constant Lambda. The inverse-image ring map is an isomorphism, so the coefficient pullback and its scalar-unit comparison tau are isomorphically the exact abelian inverse image. The ringed theorem explicitly provides the canonical direct-image isomorphism kappa and its counit equation. The text computes the transpose, then applies naturality of tau and the triangle identity. Both transposes are tau_L, which proves the desired unit equality. This is a short adjunction calculation and does not conceal a new geometric or acyclicity lemma.

Step 8 uses only the exactness clause of the existing general module-sheaf forgetful theorem. Kernel and cokernel sheafification exist on these small sites; the theorem therefore applies to both total and base sites. Conservativity is proved by the underlying zero cohomology modules, and m Lambda=0 gives torsion without Lambda being finite, flat over Z or prime-to-characteristic. In particular no injective module is asserted injective after forgetting. Step 9 instantiates the already proved argument on every Y and every L_Y, not only on inverse images of L; this verifies the full universal quantifier.

I tested the statements on the identity hypercover, the Cech nerve of a proper surjection, X empty, degree-zero matching, a non-Noetherian base, zero coefficients (m=1), a torsion ring of non-prime characteristic, negative cochain degrees and arbitrary base changes. In the empty case surjectivity forces the relevant component over a nonempty matching object; over the empty scheme all terms and the asserted unit are zero in the coefficient categories, as expected. In the identity case every composite-unit equality reduces to the identity adjunction. The generic comparison theorems keep a common lower bound and do not silently impose an upper bound. All nine steps are below 2000 characters. The B--E review eliminated the two proposed redundant inputs noted above; it found no required statement correction and leaves no unresolved mathematical step in the item. The five genuinely new inputs remain unsplit as required for a one-level delivery.

## Unfinished work

No part of the item's split is left unfinished. The five new input nodes are deliberately unsplit and join the stage-1 queue. Validation and delivery results are recorded below after the required server dry run.

## Validation

The first required server dry run exited successfully with `OK (not pushed)` at e9f78be2be. A final pass added explicit statement dependencies for Grothendieck topologies and simplicial objects to the new nodes; their mathematical statements are unchanged. Verbatim citations were refreshed. The final dry run below validates that complete packet.
