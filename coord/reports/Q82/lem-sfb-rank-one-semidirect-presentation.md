# Worker report

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-rank-one-semidirect-presentation.json`: statement, split; seven proof steps using eight existing DAG inputs. Mathlib verdict: no match after LeanFinder (two phrasings), LeanSearch, Loogle and source grep through the required msearch command. No new nodes; zero Mathlib leaves created.
- `citations.json`: one entry for each step/node citation, with the complete verbatim statement of the cited node so that multiple clauses used in one step remain visible.
- `report.md`: this report. `searches.jsonl` is the unmodified search-command log; `write_split.py` and `milne.txt` are sandbox-only working material.

## Attachments

None. I searched the live project's `lean/WeilConjectures/` for the item tag and for rank-one reductive groups, semidirect products, coroots and root subgroups. The rank-one semidirect declarations in `AlgebraicGeometry/LinearAlgebraicGroup/RankOne.lean` concern abstract extensions by the degree character, not reductive group schemes. The weights/monodromy declarations likewise do not state this item. No finished project declaration covers the item.

## WANTED

None. All mathematical sources used are available in the read-only literature directory. No source was downloaded.

## Findings and corrections

The imported statement is retained exactly, including arbitrary torus dimension, characteristic two, the given arbitrary homomorphism v, faithful flatness in the coordinate-algebra sense, and the full scheme-theoretic kernel. No statement dispute was found. The source's printed Theorem 20.33 omits the semisimple-rank-one hypothesis and misorders the derived groups; the existing classification node already corrects these issues. This split does not invoke classification or silently use its printed errors.

The formerly empty proof needed arguments that root-group checks determine the equivariance on all of SL2 and that geometric-point calculations determine the entire nonreduced kernel. I supplied two explicit standard matrix-chart factorizations for the first issue. For the second, I first exclude the complement of the a-invertible chart using the opposite-Borel intersection, then compare actual scheme coordinates over every commutative algebra. The final coordinate comparison is indispensable: geometric-point exclusion alone would miss infinitesimal kernel structure.

The source contains no theorem stated as this semidirect presentation, so proof_origin is honestly marked agent, with the source places supporting the construction. All non-elementary ingredients already have DAG statements. I did not create a new node for an elementary matrix computation or a clause of this item. The existing item search records are preserved, and the new real searches are appended. SemidirectProduct.lift (Mathlib/GroupTheory/SemidirectProduct.lean:197--204) only gives an abstract group lift after equivariance; fin_two_induction (Mathlib/LinearAlgebra/Matrix/SpecialLinearGroup.lean:387) is just matrix-entry induction. Neither is a one-line specialization giving this geometric result.

## Unfinished work

None in the proposed stage-1 split. No Lean was written and no compiler, Lake, or build tool was run. The required server dry run and delivery are recorded by the delivery tool.

## Blueprint and duplicate searches

I read the chapter and unit records, SETUP's chapter/unit/node rules and GOAL.md, and the current `literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/` unit and direct-images proof. This item remains the inherited rank-one prerequisite in the alteration/level-moduli/Haboush/root-datum chain supporting direct images, rather than a replacement route for the unit. The ancestor command returns None; I retained the existing null from.node and its detailed from.place/via chain.

Whole-blueprint searches through blueprint_refs.py for semidirect, SL2, Bruhat and rank-one found no exact counterpart (the rank-one hits concern Weil rank-one sheaves or unrelated notions). DAG searches for rank-one, root groups, Bruhat, big-cell coordinates and faithfully flat group images found the existing inputs cited here. In particular root-subgroup equivariance is already in lem-sfb-reductive-root-subgroup-parametrizations, the open scheme charts and opposite-Borel intersection are in lem-sfb-bruhat-longest-cell-charts, and arbitrary closed-subgroup tangent generation and affine coordinate faithful-flat image factorization are existing nodes. No new node is needed.

## Not duplicates

No new nodes were created, so there are no new/existing pairs to justify. The proof deliberately reuses the existing Borel root-product, Bruhat, tangent-generation and flat-image nodes.

## Review by Q82

I read delivery-errors B--E in full (both copies), the seven proposed steps and every cited node's actual statement. For the item I read Milne Proposition 20.32, Theorem 20.33, Corollary 20.34, Theorem 21.11 and paragraphs 21.19 and 21.23--21.24 in the local PDF. For the extra geometric inputs I read Corollary 10.17, Theorem 5.39, the affine Hopf-algebra theorem 3.31, the Bruhat discussion 21.70--21.73 and the big-cell theorem 21.84 with Summary 21.86. There are no new nodes needing additional sources. The proof's explicit calculations are agent expansions, not claimed verbatim source arguments.

Step 1 uses the root-parametrization statement's formulas over every test algebra, not just its existence of a root map. I verified that u_+ and u_- are isomorphisms of the precise root groups by the item's hypothesis on v. Its two matrix factorizations multiply back to M using ae-bc=1; the principal opens cover since (a,c) contains 1. The fixed diagonal relation follows from the stated coroot restriction. This removes any unsupported claim that SL2(A) is generated globally by elementary matrices for an arbitrary ring A.

Step 2 is the direct semidirect-law computation from Step 1. I checked its inverse, associativity via C(tu)=C(t)C(u), regularity of adjugates and character inverses, and finite generation of the displayed coordinate ring. No separate general semidirect-product theorem is being hidden or cited. The explicit multiplication calculation proves the morphism is a homomorphism.

Step 3 uses precisely the root character/coroot formula, the regular-cocharacter Borel statement, root-product coordinates, B=U semidirect T and the scheme-theoretic Bruhat intersection and longest-cell chart. I verified that the chosen cocharacter is regular because its integer character pairings are +2 and -2; they are not differentials and do not become zero in characteristic two. The computed n action reverses the sole positive root, so the Bruhat statement applies to this actual representative n, not a presumed preferred rank-one map. This matters because the item allows any v with the specified restrictions.

Step 4 takes the actual open immersion in the Bruhat node's statement and translates it. The matrix identity n^{-1}u_+(z)n=u_-(-z) identifies the negative factor for this given v. Reordering the Borel product is the explicit conjugation map, so the result is a scheme isomorphism with unique coordinates over nonreduced algebras. I checked that no fact from a cited node's proof, absent from its statement, is used.

Step 5 uses the affine homomorphism flat-image statement in its coordinate-algebra form. Its hypotheses require only finite-type affine group schemes over a field, verified in Step 2; they do not require smoothness of E or of its kernel. The three subgroup inclusions lift into E explicitly. The rank-one reflection node gives the full tangent weight decomposition, and the root-parametrization statement identifies the root tangent lines. T and both root groups are smooth connected closed subgroups. The tangent-generation statement explicitly permits an arbitrary, potentially nonreduced containing closed subgroup I, and therefore proves I=H rather than only an equality of reduced images. Faithful flatness then is exactly the conclusion of the flat-image statement, with no extra surjective-implies-flat inference.

Step 6 uses the scheme-theoretic opposite-Borel intersection and Borel product statements read in Steps 3--4. If n were in B after field extension, conjugation would preserve B while the intersection theorem forces B=T, contradicting the nontrivial Ga factor. In the matrix chart a=0, c is invertible over the field, and the second factorization puts v(M) in nB; that contradicts membership in T. For an arbitrary ring the elementary maximal-ideal test then shows a is a unit. This only locates the entire kernel in an open chart; no factorization through a closed subscheme is inferred from supports. Step 7 uses the previously constructed open-chart isomorphism and gives b=c=0 and t=coroot(a)^{-1} inside the actual test algebra. The inverse coordinate a is regular and invertible, and multiplication of the graph pairs verifies the group law of k. Thus every kernel and equivariance assertion is a scheme-morphism identity.

I tested the statement on H=SL2 with its diagonal torus, H=PGL2 (including characteristic two, where the usual central isogeny has nonreduced mu_2 kernel), H=GL2, and products with an arbitrary central torus. For PGL2, the mu_2 issue occurs inside the coroot map but the full kernel in E is still the graph parameterized injectively by s through d(s); no replacement by a reduced kernel occurs. For the zero test ring the matrix chart argument remains valid because its sole element is a unit. For dual-number algebras the last coordinate comparison kills off-diagonal nilpotents exactly. A rank-zero group cannot satisfy the nonempty-root hypothesis, and no minimum central-torus dimension was used.

I checked every proof step is shorter than 2000 characters and contains no long concealed lemma. The reuse of existing DAG statements resolves the non-elementary comparisons; the remaining matrix and ring manipulations are written out. Every uses entry occurs in proof_deps and has a verbatim quote in citations.json. No SGA route is used, no definition or target statement is weakened, no unit/chapter record is edited, and no file outside the assigned sandbox is written.
