# Stage-1 report: lem-trf-space-atlas-base-change-cech-geometry

## Files written

- dag/nodes/sec-trace-formula/lem-trf-space-atlas-base-change-cech-geometry.json: statement, split in five steps; no Mathlib match for the complete algebraic-space assertion.
- citations.json: one verbatim statement excerpt for each of the nine step/node pairs.
- report.md and searches.jsonl: report and actual search log. write_split.py is sandbox-only preparation.

No new nodes and no Mathlib leaves were created. The item statement and statement dependencies are unchanged.

## Attachments

None. Searched lean/WeilConjectures both for the exact blueprint tag and for AlgebraicSpace and atlas/base-change combinations. No declaration states this item. The set-Cech free resolution that a broad Cech search finds concerns sets and free modules, not this geometry. Declarations under Sheaf are not project attachments under the dispatched brief.

## WANTED

None. All sources used are present in literature/stacks-project/.

## Findings and source error

The source is spaces-morphisms.tex, Tag 03M8, lemma-compute-pushforward, especially lines 1855–1874. Its printed overlap is (V times_Y U) times_X (V times_Y U) = V times_Y R. The item already corrects the subscript to W = V times_Y X. I retained the corrected statement verbatim.

For an explicit counterexample to the printed X-subscript, let S=X=Y=U=Spec(k), with f and p identities, and let V be the disjoint union of two copies of Spec(k). The map V to Y is etale. Here Z=W=Q=V and R=Spec(k). The printed overlap Z times_X Z has four components, whereas Q has two. The actual Cech overlap Z times_W Z has two and is canonically Q. Thus no extra hypothesis on f or on V is appropriate; only the printed base is wrong. This is a source error already repaired in the assigned item, not a new statement dispute.

The source's covering sentence alone does not justify scheme representability or every structure map being etale. Those claims are now explicitly obtained from the existing fibre-product and chartwise-permanence statements. The last two steps give the inverse maps, their two projections, and the V-naturality square, rather than merely calling them canonical.

## Search and route audit

Read GOAL.md, the chapter and unit records, and the current latest blueprint chapter, unit, and lem-trf-local-term-locality statement/proof. This is a historical geometric helper beneath the section-algebra/pushforward chain, not the current unit's contracting-correspondence theorem. Its historical blueprint ancestry is retained. No unit record is changed and no alternate route is introduced. All cited statement nodes are in sk-i-curve-zero; no off-unit tool use is needed.

Whole-DAG searches for 03M8 and for Cech overlap/base-changed atlas found the item, its parent and sibling module-diagram computations; none is a substitute for proving this geometry, and no helper was created. tools/blueprint_refs.py search atlas and search 03M8 returned zero blueprint matches; ancestor returns lem-trf-local-term-locality. The item therefore retains same_as=[] and its precise existing from.place.

Ran the required search command for LeanFinder twice, Loogle, LeanSearch, and Mathlib grep. The logged queries are copied exactly into mathlib_searches. The semantic hits concern scheme covers, scheme etale base change and kernel-pair-adjacent permanence, not algebraic spaces or the enlarged site. Read Mathlib/AlgebraicGeometry/Cover/Over.lean, lines 55–105, and Mathlib/AlgebraicGeometry/Morphisms/Etale.lean, lines 50–80: all parameters there are schemes, so these cannot be one-line specializations to arbitrary algebraic spaces. The Mathlib grep for AlgebraicSpace or atlas/Cech combinations in AlgebraicGeometry returned no hits. Retained the item's inherited Q13 searches, including its unavailable LeanSearch verdict, as history; did not fabricate or re-label those calls as Q73 searches.

## Not duplicates

No new nodes; there are no new/existing same-tag pairs to justify. Reused the existing geometry/permanence/site nodes instead of introducing duplicates or extracting elementary tuple reassociation as a node.

## Review by Q73

I read the actual Tag 03M8 source, checked the wrong printed base on the two-point example above, and checked each proof step against the statements it cites. I also read spaces-properties.tex, Tags 03FR (definition-etale), 03FT (lemma-composition-etale), 03FU (lemma-base-change-etale), 03FV (lemma-etale-permanence), and 03G0 (definition-spaces-etale-site), and spaces-topologies.tex, Tag 041F (lemma-etale). There are no new nodes requiring further source review.

Step 1 uses lem-trf-space-fibre-products-etale-covers for existence and scheme representability with a scheme base, and lem-trf-space-chartwise-etale-permanence for base change and the equivalence of representable and chartwise etaleness when the source is a scheme. For R the scheme base is U and the etale leg is p; for Z it is U and v; for Q it is R and v. The map W to X is the base change of v, and no claim that W is a scheme is made. Both projections of R are base changes of p. These are exactly the hypotheses of the cited statements.

Step 2 uses the fibre-product node's actual universal property and its jointly-surjective-etale-family pullback conclusion. Its isomorphism Z = W times_X U is written on coordinates, including its inverse, over W. Thus the pulled-back family really is the named singleton Z to W; surjectivity is not inferred merely from etaleness.

Step 3 uses chartwise composition for the maps to X and the enlarged-site node's explicit description of objects, arrows and coverings. I read that description, not just its title or its sheaf equivalence. Q to X is the composite Q to R to U to X; likewise Z and R have the indicated composites. Every listed arrow commutes with these maps to X. This covers the site-membership clause without assuming that f itself is etale.

Step 4 uses the fibre-product node's sheaf/categorical fibre product and def-trf-algebraic-space's statement that morphisms are natural transformations. Equality over W imposes BOTH v_1=v_2 and pu_1=pu_2. The forward and inverse formulas preserve exactly those conditions and the Y-condition. Both composites are the identity, the maps commute with restriction in T, and the two maps to Z are precisely those induced by p_1 and p_2. This is an elementary compatible-pair calculation, not an uncited geometric theorem or a use of a dependency's proof.

Step 5 uses the same universal property and natural-transformation definition. For a:V' to V over Y, either route sends the displayed tuple to (a v'_T,(u_1,u_2)). This proves the stated naturality, including its inverse, on every test scheme. The argument works even for arbitrary maps V' to V over Y when both are allowed tests, so in particular for the requested etale test maps.

Checked empty X, empty V, identity atlas, and a disconnected noninjective etale V. Empty cases have empty corresponding products and a legitimate singleton covering of the empty target; no nonemptiness, quasi-compactness, separatedness or affine hypothesis is used. The two-point example also checks that the equalities are imposed over W rather than just X. The conclusions about Q to X and its projections need only the cited composition/property statements.

Against delivery-errors B: there are no new unsplit nodes or Mathlib leaves; all notions in the item retain their definition dependencies, TeX is singly escaped in parsed JSON, and the source tag and label were checked. Against C: read every cited statement, supplied verbatim excerpts for every use, and checked dependency closures for cycles. Against D: the steps contain the actual argument and no restated-clause node was introduced. Against E: checked the bases of each pullback, all representability hypotheses, both overlap conditions, the explicit inverse and the naturality square. No step exceeds 2000 characters (lengths 541, 481, 495, 718, 521), so no long step hides another lemma. No prohibited SGA source is used. All work is sandbox-only; no Lean was written and no compiler, Lake, local DAG checker, or repository git command was run.

## Unfinished work

None in the mathematical split. Required server dry run and delivery are run after this report is written.
