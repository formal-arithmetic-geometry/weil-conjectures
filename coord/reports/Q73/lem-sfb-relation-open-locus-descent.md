# Stage-1 delivery: lem-sfb-relation-open-locus-descent

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-relation-open-locus-descent.json: statement, split; no exact Mathlib match after recorded LeanFinder, Loogle, LeanSearch and source-grep searches, including a second phrasing.
- citations.json: ten verbatim statement excerpts, one for each citation in each proof step.
- report.md: this report. searches.jsonl is the unmodified search-command log.

New nodes: 0. New Mathlib leaves: 0.

## Attachments

None. Searched the project WeilConjectures source for the exact blueprint tag, groupoid/locus combinations, scheme-equivalence-relation language and groupoid translation. No declaration states the assigned-locus descent conclusion. Existing source lemmas about special loci do not imply the arbitrary assignment in this item.

## WANTED

None. All mathematical sources used are available locally.

## Corrections and scope

The statement is unchanged. The original node had no proof. The source is Stacks Tag 04LH, more-groupoids.tex, lemma-local-source, with g=id. Although that lemma phrases its hypothesis using a largest property locus, its proof uses only base-change compatibility and invariance under isomorphisms, exactly the hypotheses here. No largest-open assumption is needed for this item.

Read the current latest blueprint unit in sec-six-functors-basics/sk-thm-sf-ctf-stability and its direct-images proof (3). The node's inherited ancestry refers to a longer historical alteration prerequisite route; this technical lemma has no individual blueprint counterpart. Retained the ancestry, including its null from.node as returned by blueprint_refs.py ancestor, and described the place precisely. The blueprint searches for local-source, source-open locus, groupoid, translation, equivalence relation, division and Tag 03C6 found no same statement. The unit record is not rewritten: this item is not its key statement.

Tool use: lem-a1-groupoid-source-pullback-translation is a generic scheme-groupoid isomorphism from another unit. It is declared in split_report.tool_uses. Its rank-stratum consequence is not used. No alternative alteration or coefficient route is introduced.

## Not duplicates

No new nodes. In particular I did not create a second groupoid division-cartesian lemma: inversion and swapping the factors of the existing translation isomorphism supply it. lem-sfb-groupoid-quasifinite-locus-descent shares Tag 04LH but concerns a specific quasi-finite locus and a general auxiliary g; it is not a statement of this arbitrary-locus assignment. lem-sfb-groupoid-diagonal-two-pullback-identities concerns diagonals of fibred categories and does not give these scheme division squares. The existing coinduction-adjunction node cites Tag 03C6 in its proof but its statement is an adjunction for quasi-coherent modules, so it cannot supply the diagram.

## Review by Q73

I read Stacks more-groupoids.tex, Tag 04LH (lemma-local-source), its full displayed diagram and the identity-section conclusion; groupoids.tex, Tags 0233 (lemma-equivalence-groupoid), 02YE (lemma-diagram), and 03C6 (lemma-diagram-pull); and morphisms.tex, Tags 01U9 and 01TS for the base-change stability hypotheses. I also read the exact statements of every cited DAG node, rather than relying on the tags in their proofs. There are no new-node sources to audit.

Step 1 uses the actual natural Hom(h_X,F) bijection stated by lem-pc-yoneda, not merely full faithfulness of h. Reflexivity, symmetry and transitivity supply unique operations on test-scheme points. Their naturality follows from uniqueness of the arrow with given endpoints, and evaluation at the identity represents them by scheme morphisms. The fibre-product statement provides the composition domain. def-a1-groupoid-scheme lists precisely the laws checked on endpoints; it is used as a definition, not as a theorem about cartesian diagrams. The S-relative version uses Yoneda on Sch/S as the cited statement explicitly allows.

Step 2 uses exactly the isomorphism F:P to Q and inverse G in lem-a1-groupoid-source-pullback-translation. I checked the orientation with c(a,b)=a composed with b. On A=R times_{t,V,t} R the division d=i(a) composed with b has source s(b) and target s(a). Applying G to (i(b),i(a)) and then inverting both output factors gives (d,a) in R times_{t,V,s} R. Applying G to (i(a),i(b)) and then inverting its second factor gives (d,b) in R times_{s,V,s} R. These identifications are isomorphisms by the cited translation and the groupoid inverse laws. The text gives both inverse formulas, so cartesianness is not an uncited appeal to the omitted exercise in Tag 02YE. Each square has top d and bottom s, with vertical maps respectively (p0,t) and (p1,s).

Step 3 uses the flat-base-change statement of lem-weil-pbc-flat-morphism-base-change and clause (3), specifically local finite presentation under arbitrary base change, of lem-weil-pbc-qcqs-morphism-permanence. The extra qcqs assertions of that node are not used. I checked all three morphisms in each assignment square: s is flat and locally finitely presented by hypothesis, the base morphism is s or t and has the same hypotheses, and d is the corresponding base change and therefore also has both properties. Invariance under isomorphisms of morphisms is needed because the two pullbacks are represented on the same scheme A via different isomorphisms; it is explicitly assumed. This gives the equality of the two pulled-back opens, without applying the assignment to the possibly nonflat identity section e.

Step 4 uses only the universal property of def-pc-fibre-product and the restricted-structure-sheaf meaning of def-weil-open-immersion. The section graph j=(id,e t) lands in the fibre product because t e t=t. Its composites with the two projections are id and e t, so pulling back the equality is the explicit calculation D_s=(e t)^{-1}D_s=t^{-1}W. Continuous inverse images are open. Equality of the open subsets identifies the actual open subschemes, not only their point sets with an unspecified structure sheaf.

For the B--E checklist I verified self-contained hypotheses, accurate source labels and tags, no new statement-only nodes that disguise clauses, no unrecorded searches, and all ten citation quotes as literal substrings of the cited statements. The only non-elementary imported black boxes are cited. No step exceeds 2000 characters (lengths 589, 866, 620, 564); the four-step argument totals 2639 characters. No additional elementary node is created. The empty scheme makes every equality empty. The diagonal relation has s=t=e=id and the conclusion is tautological. The indiscrete pair relation has d(a,b) the arrow between the sources, confirming the source/target orientation. Nonreduced schemes cause no pointwise shortcut: the cartesian and inverse identities are morphism identities checked on all test schemes. Flatness of e, quasi-compactness and any largest-open condition are not used.

## Unfinished work

None in this stage-1 split. Mechanical dry run and push results are recorded below once completed.
