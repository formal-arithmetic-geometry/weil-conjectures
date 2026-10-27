# Q89: lem-sfb-dg-qis-restriction-equivalence

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dg-qis-restriction-equivalence.json: item, split following Stacks 09S6, five assembly steps; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-dg-bimodule-derived-adjunction.json: statement-only lemma, unsplit, no Mathlib match. Arbitrary unbounded DG bimodule tensor/Hom construction and exact adjunction, without a quasi-isomorphism assumption.
- dag/nodes/sec-six-functors-basics/lem-sfb-dg-compact-bimodule-full-faithfulness.json: statement-only lemma, unsplit, no Mathlib match. Stacks 09R9 for an arbitrary compact bimodule, with no generation assumption.
- citations.json: verbatim statements for each cited node in each item proof step.

## Attachments

None. Searches of lean/WeilConjectures for the item tag, DGAlgebra, DGModule, differential graded and quasi-isomorphism/restriction notions found no declaration stating this theorem. Ordinary complex and change-of-rings results do not state its DG-algebra conclusion.

## WANTED

None. All source material newly required for this split is in literature/stacks-project/dga.tex and derived.tex. The existing enriched Yoneda node is reused as a statement, not reproved from its external references.

## Source error

The item's statement agrees with Tag 09S6 and has not changed. Example 0BYX, example-map-hom-tensor, calls RHom(B,-) the *left* adjoint of tensor in its prose. Lemma 09LT and the displayed Hom-set equality in the same example give the opposite, correct direction: tensor is left adjoint to RHom. The proof of 09R9 also says 'left adjoint' in its opening sentence but uses the unit M to RHom(N,M tensor N), hence the same correct adjunction. The split follows the formulas and 09LT, not these directional typos. No added hypothesis or weakened conclusion is involved.

The imported item has a null blueprint ancestor, with a long inherited via chain. blueprint_refs.py ancestor returns None. I retained that value and lineage, with an explicit place for the supporting inputs. I read the current latest blueprint's sk-thm-sf-ctf-stability unit and sk-thm-sf-ctf-stability-direct-images.proof.md (3), and the recorded chapter/unit JSON. This is a foundation beneath its inherited coherent-family/Quot route; no chapter or unit argument is replaced and this is not the unit's key node.

## Not duplicates

lem-sfb-dg-bimodule-derived-adjunction vs lem-trf-derived-bimodule-tensor-hom: the latter is an internal derived-Hom comparison for ordinary commutative rings S to B, retaining S-scalars; it does not construct the unbounded derived tensor and Hom functors for arbitrary DG A and DG B and an arbitrary DG bimodule.
lem-sfb-dg-bimodule-derived-adjunction vs lem-trf-bimodule-adjunction-evaluation-scalars: that statement fixes an ordinary commutative ring map and a K-flat B-complex Q and gives the S-linear adjunction U(- tensor Q) with coinduced Hom; it does not give the arbitrary DG-bimodule construction here.
lem-sfb-dg-bimodule-derived-adjunction vs lem-trf-perfect-algebra-dual-evaluation: the latter is a duality isomorphism for a perfect ordinary commutative S-algebra B, not the unbounded DG tensor/Hom construction with no perfectness assumption.

The 09LT same-tag nodes above were all opened and read. Searches of the whole DAG by these tags, by the labels and by the DG/bimodule concepts, and blueprint_refs.py searches for differential graded, 09R9, 09LT, compact bimodule, compact fully faithful, derived tensor bimodule, tensor adjunction and restriction scalars found no blueprint duplicate. The compact-bundle self-Ext node is about an ordinary degree-zero endomorphism ring acting on a vector bundle on a scheme; it is not a general DG-bimodule criterion. The free rank-one calculation would duplicate the existing lem-coef-derived-enriched-yoneda, so I did not create that proposed node. Compactness of the free module uses the existing finite-cell node. The zero-kernel step uses the existing exact-adjoint criterion. Neither new node restates equivalence or assumes that A to B is a quasi-isomorphism.

## Review by Q89

I read Stacks 09S6 (lemma-qis-equivalence), its proof and supporting 09LT (lemma-tensor-hom-adjoint), 0BYX (example-map-hom-tensor) and 09R9 (lemma-tensor-with-compact-fully-faithful) in dga.tex, checking the tag-label mapping. For the new adjunction node I also read the balanced tensor and Hom constructions, their no-sign shift comparisons, 09LS (derived tensor), 09LI (derived Hom), the chain currying statement 09LN, and the derived-adjunction argument in derived.tex. For the compact-bimodule node I read all of 09R9's statement and proof. Each new node states a general input used by the proof, with its own objects and hypotheses, and carries no proof sketch or dependency proof. Its proof is intentionally left for its future worker.

Step 1 uses only the new adjunction node: I checked it actually gives existence of both unbounded functors, the homotopically injective Hom model, exactness, and the shift-compatible adjunction. The displayed evaluation and inverse are written out rather than attributed to a definition node. A homogeneous right-B-linear map is determined by its value at 1; the differential and A-action computations verify that the identification is one of DG A-modules. Restriction preserves the resolution quasi-isomorphism because the complexes are unchanged. This works for noncommutative graded A and B and needs no flatness of B over A.

Step 2 cites the existing finite-cell compactness statement, which I opened: for the algebra B use the single filtration 0 contained in B, so its single quotient is one shift-zero copy of B. This supplies precisely coproduct compactness, not finite presentation or a topological notion of compactness.

Step 3 cites lem-coef-derived-enriched-yoneda and the new 09R9 node. I opened the former and checked that it states the derived evaluation equivalence RHom(h_X,P) equivalent to P(X), not merely full faithfulness of the Yoneda embedding. Specializing to the one-object DG category with endomorphism algebra B makes its representable module B and evaluates to B. Taking H^k gives Hom(B,B[k]) equal to H^k(B). I checked the map as well as the groups: a cycle a acts by left multiplication by phi(a), and evaluation at 1 gives phi(a). Hence the actual map required in 09R9 is the assumed H^k(phi). The hypotheses of the new 09R9 node are now both verified. No generation, countability, nonpositive grading or ordinary-ring restriction has entered. The Yoneda node is an off-unit generic tool; split_report.tool_uses explains why this unit needs precisely its statement. Its dependency closure has no path back to the item, so this is not circular.

Step 4 has no citation: H^k(RY) and H^k(Y) are the same groups by the definition of restriction. If the former vanish, the actual map 0 to Y is a quasi-isomorphism and is inverted by the definition of D(B,d). Thus the zero-kernel assertion is an elementary step, not a new node and not an unjustified conservativity theorem.

Step 5 cites lem-sfb-exact-adjoint-zero-kernel-equivalence, whose full statement I opened. It assumes exact F and G, specified F left adjoint to G, full faithfulness of F, and G detecting zero objects, and concludes that the unit and counit of that specified adjunction are natural isomorphisms. These are exactly Steps 1, 3 and 4 with F=L and G=R. Its statement gives both unit and counit, rather than only an unspecified equivalence. The final triangle and shift compatibility already comes from Step 1's exact adjunction and evaluation comparison, not from an uncited assertion about arbitrary category equivalences. I checked the closures of this node and the finite-cell node for cycles as well.

Small cases checked: phi equal to the identity; ordinary noncommutative rings in degree zero; the zero algebra and acyclic unital DG algebras; shifts of the free module in negative and positive degrees; a non-generator compact bimodule for 09R9 (no essential-surjectivity conclusion is claimed there); and a general non-quasi-isomorphism A to B for the adjunction input (no equivalence conclusion is claimed). For an acyclic unital algebra, the identity of any DG module is null-homotopic by a primitive of the unit, agreeing with its zero derived category. Negative grading and unbounded modules cause no boundedness assumption in either supporting lemma. The example Z to Z/2 is not a quasi-isomorphism and is correctly excluded from the item while still allowed in the adjunction input.

Mathlib searches were run through msearch.py and their logged outputs read; the two new nodes record their exact tool/query pairs with verdicts and the log records themselves as results. Each has leanfinder, leansearch, loogle and grep, with a second semantic phrasing. I read candidate ordinary ModuleCat.extendRestrictScalarsAdj, generic Adjunction.derived and the ordinary K-projective localization comparison: none constructs arbitrary DG algebra module categories or supplies the compact-bimodule criterion. DifferentialObject.lean identifies complexes with differential objects, not DG modules over an algebra. No successful query is recorded as unavailable, and no unrun query is recorded.

I checked delivery-errors B through E against each file and source: statements are self-contained, use single TeX escapes, cite the actual definition nodes or define notions inline, have exact tag-label sources and searched blueprint lineage, and keep the new nodes statement-only. Every non-elementary item input is a cited statement and every proof citation has a verbatim quote in citations.json. There is no elementary new lemma, duplicate free-module node, relabelled equivalence clause, hidden inline comparison, circular dependency or unverified additional hypothesis. All five proof steps are under 2000 characters; the total assembly text is under 3000 characters. No SGA source is used. I have written only in this item's sandbox and have run no Lean, compiler, Lake, local DAG validator or git command.

## Unfinished

None in the authorized one-level split. The two supporting statement-only nodes are deliberately unsplit for future stage-1 work. Delivery validation results are appended below after the required dry run.

The first dry run rejected the deictic phrase “the item's hypothesis” in proof step 3. I replaced it with “the assumed isomorphisms on cohomology”, which names the hypothesis directly. No statement or argument changed. I also recorded the two additional arbitrary-DG-bimodule search outputs after reading them.
