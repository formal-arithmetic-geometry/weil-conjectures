# Worker report

## Files written

- `dag/nodes/sec-six-functors/lem-coef-operadic-collage-segal-mapping-bridge.json`: five-step stage-1 split, statement unchanged, using existing DAG nodes only.
- `citations.json`: 18 verbatim excerpts covering all 17 step/node citations, including both clauses of the pointwise-limit/representable theorem used in step 3.
- `searches.jsonl`: retained the earlier command log; additional searches address the repaired varying-base argument. The exact executed queries and results are recorded in the item's `mathlib_searches`.

## New nodes

None. The never-committed `lem-coef-square-fiberwise-homotopy-pullback` draft is saved under `prior-attempt/`, together with the preceding report and citations. Its square criterion is a short application of the existing `lem-coef-spaces-homotopy-fiber-detection` over the identity base, after mapping-path replacement, so it should not enter the DAG as another node. Its previous search results remain available in `searches.jsonl`.

## Attachments

None. Searches in `/home/ubuntu/weil-src-slopmaster2/WeilConjectures/` for the blueprint id and for constant-source, Segal/mapping, homotopy-pullback/fibre and mapping-limit terminology found no declaration stating the item. The homotopy-limit hits in IntegralCoefficients/IntegralCoefficient and Triangulated/HomotopyLimit concern towers in ordinary triangulated categories, not coherent functor quasicategories, and cannot attach this item.

## Wanted sources

WANTED: an archived copy of Gepner--Haugseng, *Enriched infinity-Categories via Nonsymmetric infinity-Operads*, arXiv:1312.3178v4, Definition A.3.1(2) and Remark A.4.2, for this item's relative Segal/mapping-cylinder application.

WANTED: archived HTT, Corollary 3.3.3.4 and Remark 3.3.3.5 (section/limit comparison), and Proposition 5.1.2.2, Corollary 5.1.2.3 and Proposition 5.1.3.2 (pointwise limits and representables), for the existing nodes used in steps 1 and 3.

WANTED: archived Kerodon 00ZN, 0101, 0328 and 0329, for the existing fibre-detection, mapping-path and strict-to-homotopy-pullback results used in step 4. These are Kerodon identifiers, not Stacks tags. No matching Stacks result is being asserted.

## Corrections to the earlier attempt

The initial required dry run completed with exit 1 and pushed nothing. Its two failures were the new square node's missing definition citations and Unicode mathematical notation. Reviewing that draft against the entire DAG found that no new square node is necessary; the final split writes its short application directly in step 4 with the existing results cited.

There was also a C4/E1 error in the earlier proof's use of `lem-coef-infinity-edge-pullback-mapping-fiber`: that node assumes both diagrams lie in fibres over fixed base objects. Here `pf` need not be constant. For example, take the ordinary base `[1]`, `r=1`, put the edge object of `I_1` over 0 and both vertex objects over 1, and take the cone apex and `pz` over 0. The pullback over the identity arrow at 0 cannot contain the vertex values over 1. Thus the earlier attempted invocation was ill-typed. Also, the target point in `D` is `(p lambda) composed with Delta(phi)`, not `Delta(phi)`. Steps 2 and 3 now write that transformation and all its varying components explicitly, using a pointwise pullback of space-valued diagrams. This corrects the proof; the imported statement itself remains true and unchanged.

The previous `proof_origin.by = document` overstated what the cited operadic definition proves. The replacement proof is explicitly marked agent-written: it expands the mapping-cylinder verification from the named existing mathematical statements, rather than claiming Definition A.3.1 supplies this proof verbatim. Original item provenance and the full ancestry chain are retained.

## Not duplicates

No new nodes are delivered. Searches of the whole DAG by statement text, homotopy-fibre/pullback/limit terminology, and blueprint searches for `incidence`, `homotopy pullback`, `limits commute`, and `fiber` locate the existing section, Yoneda/pointwise-limit, and fibre-detection statements used here. The superseded square draft adds no needed independent lemma beyond those statements.

## Review by Q111

I read the item in the current shared repository and compared it with the sandbox, read the chapter and `sk-prop-sf-biduality-general` records, and followed the recorded historical ancestry to `prop-coef-integral-exceptional-adjoint`. The item's finite incidence shape is a supporting calculation in the rectification/free-operad/collage chain, not a new coefficient-category identification. I read online Gepner--Haugseng Definition A.3.1(2), which imposes the relative limit condition, and Remark A.4.2, which constructs the mapping cylinder. Neither text states the present mapping-space expansion verbatim; that is why this delivery records an agent proof. I also read online Kerodon 00ZN, 0101, 0328 and 0329 and checked the fibre test and replacement hypotheses against their statements. I did not use the forbidden SGA route or change a unit or chapter.

For step 1 I opened the complete statements of `lem-coef-infinity-constant-source-section-comparison`, `lem-coef-space-transport-classification`, and `lem-coef-right-fibration-section-limit`. The first gives precisely the constant-source mapping space as maps from the terminal diagram in spaces. The second's dual classification, constant-functor clause and mapping-space formula identify those maps with sections of the right fibration over `K` opposite. The third identifies those sections, with their evaluations, as the limit over `K`. This avoids the earlier unexplained comparison between a Kan complex and its opposite. The mapping-bifunctor clause specifies postcomposition on each incidence arrow. The smallness hypotheses hold by choosing universes containing `X`, `B` and their mapping spaces; `I_r` is finite and its nerve is small.

For step 2 I opened the cone definition and the mapping-bifunctor composition clause. This step only defines the four mapping spaces and computes the actual image of phi as the composite with `p lambda`. It makes no fixed-base assumption. The written component formula checks each of the two arrows from every edge object, and the coherent transformation supplies their compatibility. This is elementary composition of the cited data.

For step 3 I read `lem-coef-infinity-yoneda-presheaf-limits` in full, not just its fully-faithful-Yoneda sentence. Its statement actually says that space-valued functor categories have small limits computed objectwise and that covariant representable mapping-space functors preserve all existing small limits. Thus `F` pulled back over `G` along the particular section has the displayed pointwise homotopy fibres, and maps from the terminal diagram preserve that pullback. The terminal object's endomorphism space is contractible by its defining universal property; the resulting pullback is the fibre over the chosen section. Step 1 then gives its limit of pointwise fibres. The path model used for fibres is supported by the homotopy-pullback replacement clause of `lem-coef-kan-quillen-right-proper`, whose statement I also read. There is no use of the edge-pullback lemma or of an unproved interchange theorem.

For step 4 I opened the homotopy-pullback definition and the full statements of `lem-coef-space-path-fibration-replacement`, `lem-coef-kan-pullback-path-comparison`, and `lem-coef-spaces-homotopy-fiber-detection`. The first makes the path replacement of `V -> D` a Kan fibration. Pullback stability is justified directly by transporting a horn lifting problem; no extra theorem is silently invoked. The second identifies the strict vertex fibre with the homotopy fibre of the projection. The displayed coordinates show the strict fibre is exactly the fibre of `V -> D` over the composite transformation computed in step 2. The third applies to the comparison `U -> P` with bottom map the identity of `C`, which is an equivalence; it allows nonfibrational `U -> C` and empty fibres. Hence it proves exactly the two-way square test. The proposed new arbitrary-square statement is folded into this short application, rather than relabelling the item's clause as a new node.

For step 5 I checked the constant-source node's explicit postcomposition formula and naturality clauses, the transport node's composition/unit coherences, the right-fibration theorem's evaluation and restriction naturality, and the Yoneda theorem's naturality in diagrams and testing objects. These identify the actual fibre maps with `u -> (lambda_alpha u)` and preserve all their evaluation projections. Naturality of the path part is direct from its specified coordinate maps. This is verification of the comparison already constructed in steps 1--4, not an extra uncited equivalence claim.

I checked `r=0` (one vertex), empty mapping spaces, an empty `C` (both `U` and its comparison pullback are empty), identity base arrows, and the nonconstant `[1]` example above. No new statement or notion is introduced. The proof happens to use a general space-valued-diagram argument; it retains all the item's inner-fibration and ordinary-base hypotheses. Every proof step is below 2000 characters. Every cited statement is quoted verbatim in `citations.json`; both pointwise-limit and representable-preservation clauses are quoted separately for step 3. Mathlib search hits were read as returned: ordinary Hom-set limit formulas, ordinary simplicial pullbacks, fibrant objects and path objects do not state this coherent mapping-space result. Invalid earlier Loogle patterns are not evidence of absence; valid additional Loogle, semantic and source-grep queries were run and logged. No Lean files or compiler/build tools were used.

## Unfinished work

No mathematical part of the one-level split is left pending. Delivery validation is run on the server by the authorized delivery wrapper; the maintainer remains the independent reviewer.
