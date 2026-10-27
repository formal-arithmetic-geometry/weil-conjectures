# Q17 stage-1 report: lem-wf-common-stage-point-return

1. Files written: dag/nodes/sec-deligne-laumon-a1/lem-wf-common-stage-point-return.json (statement preserved, five-step split, no Mathlib match); citations.json (11 checked verbatim step citations); report.md. No new nodes and no Mathlib leaves.
2. Attachments: none. Searched lean/WeilConjectures by the exact blueprint tag and point-transport, semilinear-return and common-stage terminology. StageSystem and filtered two-colimit files are generic infrastructure, not declarations of this full normalized adic assertion.
3. WANTED: none. No new literature theorem is needed.
4. The item had no proof. Its finite-stage content already occurs, with the same normalization and no Tor restriction, in lem-trf-local-frobenius-transport-normalization. Reused that existing statement rather than creating clause nodes. The common-stage representative calculation is now explicit. The statement, semilinear return, literal pair category and full bounded-constructible scope are unchanged.
5. Nothing mathematical remains unfinished in this split. Delivery validation is run after this report is written. No Lean was written and no compiler, Lake or build was run.

## Sources and route

Read the chapter record sec-deligne-laumon-a1 and unit sk-l-dl-a1-energy. This auxiliary item serves the punctual-Frobenius comparison in the opening sentence of lem-wf-l2-upper, through lem-wf-rational-stalk-exact; it is not the key statement of the energy unit, so no unit record is modified. Read the current main-20261015 lem-wf-l2-upper text and prop-trf-karoubi-independence.proof.md. The latter's last sentence asserts Frobenius transport without this argument; our proof is explicitly agent-written assembly, not a claim that its trace theorem proves arbitrary-complex transport. In particular no perfectness assumption or trace identity is used.

Read the complete statements of every cited node, including the precise strict-system normalization in lem-trf-integral-pullback-comparison-realization, the rational part of lem-weil-point-sections-scalar-extension, and the final coefficient equation of lem-trf-local-frobenius-transport-normalization. These existing extracted comparison results supply the non-elementary inputs. No SGA source is used.

## Searches and reuse

Read and retained the item's earlier Mathlib searches. Ran and read the five additional searches recorded verbatim in searches.jsonl and appended them to mathlib_searches: grep, LeanSearch, Loogle and two distinct LeanFinder phrasings. All services answered. Hits concern generic natural transformations, field Frobenius, site-point fibre functors and condensed colimits, not the specified normalized rational adic transport assertion. None gives the item by one-line specialization.

Searched the whole DAG for point transport and comparison statements and the blueprint through blueprint_refs.py searches for point transport, semilinear return and common-stage; checked the ancestor. No blueprint node states the complete item in another form. Existing local normalization is the exact finite-stage input and was reused. No new node needed a fresh statement search. Checked the dependency closures of the three nontrivial comparison inputs; none reaches this item.

## Not duplicates

No new nodes were created. The existing lem-trf-local-frobenius-transport-normalization provides finite-stage transport, while this item additionally constructs the point functor and the natural return transformation on the literal common-stage category. We cite it and give the remaining argument instead of creating a duplicate.

## Review by Q17

I checked B through E of delivery-errors.md against the statement and all five steps. There are no new statement-only nodes, no hollow constructions, no unrun searches and no new Stacks-tag claims. Every displayed arrow is in the rational categories actually named by the item. The two pair categories are read from their own definition nodes; the source is not silently replaced by a Karoubi completion or a category with strict coefficient transitions.

Step 1 uses the natural pullback scalar comparison and its normalized unit/tower laws from lem-trf-integral-pullback-comparison-realization, the natural rational sections comparison and its tower law from lem-weil-point-sections-scalar-extension, and the rational point-functor action of def-weil-finite-coefficient-point. I checked the direction: beta is the inverse sections comparison, so Fib(a) beta maps the extended old fibre TO the fibre of the extended complex. Naturality allows the middle factors in a tower to be commuted and the two tower laws then combine them. These inputs are natural for arbitrary rational morphisms, not just sheaf maps.

Step 2 uses exactly the statement of lem-trf-local-frobenius-transport-normalization with X_0=Y_0, m=n and y=x. Its t is the same map as J, including the normalized return in def-weil-local-frobenius-trace. I verified separated finite type, the characteristic restriction, the rational coefficient stage, n positive, and the absence of a Weil-structure hypothesis. The cited final equation has P_M(d_n) on the correct side. Its explicit no-finite-Tor condition covers the entire intended domain. This is a reuse of an existing theorem, not an appeal to its proof.

Step 3 writes the actual descended arrow b_target inverse P_M(u) b_source and checks both transition independence and composition. The common-stage equality criteria are explicitly stated by def-weil-algebraically-closed-coefficients and def-weil-point-fd-qlbar-category. The only algebra is substitution of step 1's tower/naturality equations and cancellation of inverse comparisons. No injectivity of scalar extension on Hom groups is assumed: equality is tested at a further common field. Point-functor values are bounded finite dimensional by the already defined finite-coefficient point functor.

Step 4 uses the common-stage pullback action given in def-weil-derived-pullback-tensor-hom, with its comparisons fixed by lem-trf-integral-pullback-comparison-realization, and the finite-stage scalar and naturality equations of lem-trf-local-frobenius-transport-normalization. I expanded the three equalities: substitute D times the extended J, use finite-stage naturality for the representative u, and substitute the target scalar equation backwards. This checks the actual compatibility rather than merely saying that transport commutes. Both sides are computed in the same D(M).

Step 5 uses the target Hom-colimit equality criterion of def-weil-point-fd-qlbar-category together with steps 2 and 4. Extending their equality and its associators identifies different representatives at a common N, which proves naturality and independence. The literal objects are pairs: independence means the specified transition isomorphisms intertwine J, not that pairs become equal objects. I checked n=1, equality of coefficient fields, zero complexes, zero morphisms, torsion integral representatives whose rationalizations vanish, noninvertible underlying morphisms, different finite fields, and empty rational-point sets (there is then no chosen x). No argument replaces the semilinear equality by a fixed geometric-point equality. No Weil-stable lattice is chosen. No new hypotheses or weakened conclusions were introduced.

All steps are shorter than 2000 characters. Steps 1 and 2 are marked non-elementary because they use the existing comparison theorems; steps 3 through 5 consist of written representative algebra using those established inputs. The three off-unit comparison lemmas are declared in split_report.tool_uses with their purpose; they are tools for this punctual-Frobenius construction and do not replace the energy unit's route. I checked each citation quote as a verbatim substring of the cited live statement before writing citations.json. The original statement needs no STATEMENT-DISPUTED repair.

## Validation repair

The first delivery dry run rejected the return-equality quote as shorter than 40 characters; nothing was pushed. Replaced it with the complete semilinear-return sentence and formula from def-weil-local-frobenius-trace. Also expanded the local-normalization and point-functor quotes to their complete relevant paragraphs. Verified all 11 quotes again; the mathematical split is unchanged. The standalone server check_dag and review_split checks passed before this citation-length repair.
