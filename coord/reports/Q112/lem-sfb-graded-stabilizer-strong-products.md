# Stage-1 report: lem-sfb-graded-stabilizer-strong-products

1. Files written:
   - dag/nodes/sec-six-functors-basics/lem-sfb-graded-stabilizer-strong-products.json: item split into five explicit steps, statement unchanged, no Mathlib match.
   - dag/nodes/sec-six-functors-basics/lem-sfb-homogeneous-maximal-graded-field-quotient.json: one new statement-only algebra lemma, unsplit, no Mathlib match.
   - citations.json: four citations, verbatim from the two statements used.
   - searches.jsonl and search-0.txt through search-9.txt: actual prescribed searches and their stdout; no fabricated or edited search records.
2. Attachments: none. Exact blueprint-tag and stabilizer/strong-grading searches in lean/WeilConjectures found no theorem asserting the item. Graded module, homogeneous localization, and profinite ideal stabilizer declarations are different statements. No compiler or Lean-writing tool was used.
3. WANTED: Abramovich–Temkin, Luna's fundamental lemma for diagonalizable groups, Lemma 5.4.4, the contextual source already requested in the Q20 report. It is not used as a theorem in this split. No missing external result is assumed. The proof is explicitly agent-written.
4. What was wrong: the live item is a statement-only auxiliary. Its source correctly says Stacks 0EKK does not state the assertion. Q20's complete retained report gives a residue-field/base-change proof; here the simpler ideal KA replaces that reduction, keeping the same graded-field and coefficient argument. This avoids silently requiring flatness or a base-change lemma. There is no mathematical statement dispute and no changed hypothesis or conclusion. No repair note exists for this item. The sandbox had no item, report or searches at the start, so the live item and the Q20 retained argument were read and reused. Historical searches in the live node are preserved, with new searches appended.
5. What remains: the one new statement-only node joins the queue. Its full natural-language proof is retained below. The item is not the unit's key statement, so no unit realization fields are written. All writes are confined to the named sandbox; there was no git command in the shared repository and no launcher modification.

## Source and route

I read the chapter and unit records, the three-level rule in SETUP.md, the current latest blueprint unit and its proof at literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/, and coord/reports/Q20/lem-sfb-affine-free-split-torus-invariants.md. This item is the subsidiary affine-chart quotient algebra tool along its inherited via chain. blueprint_refs.py ancestor returns None, as it did for its creator; I preserve the null ancestor and extend its exact via chain for the child. The current unit concerns six-functor preservation; this is not a replacement for a unit step, and no chapter or unit route is changed.

For the item I read Stacks groupoids.tex Tag 0EKK, label lemma-complete-reducibility-Gm, including the coaction coefficient argument. It concerns the grading interpretation of G_m actions only. Our arbitrary abelian-group grading and ideal implication are proved algebraically rather than attributed to that source. For the new node I read algebra.tex Tag 00JM, label section-proj, especially the componentwise definition of homogeneous ideals. Its nonnegative grading conventions are not silently applied to M: the new statement explicitly defines the group grading and homogeneous ideals, and the generalization and Zorn proof are agent-written. The source field states this limitation explicitly.

## Complete proof retained for the new node

Let A, M and a proper homogeneous ideal L be as in the new statement. Order the proper homogeneous ideals containing L by inclusion. It is a nonempty set (it contains L). The union of a nonempty chain is an ideal: for two elements choose a chain member containing both, then use its ideal operations. It is homogeneous because the chain member containing an element contains each of its homogeneous components. The union is proper since otherwise it would contain 1, which would already belong to a proper member. An empty chain has upper bound L. Zorn's lemma gives a maximal member H.

Let q:A to D=A/H be the quotient map. Its images D_n=q(A_n) additively generate D with finite supports. If a finite sum of homogeneous lifts a_n maps to zero, the sum lies in H; homogeneity of H puts every a_n in H. Thus the sum of the D_n is direct. The unit and multiplication laws descend because q is a ring homomorphism. Since H is proper, D is nonzero.

For nonzero d in D_n choose a homogeneous lift a in A_n. The ideal H+(a) is homogeneous: a finite expression h+ax decomposes degree r as h_r+a x_(r-n), which is again in H+(a). It strictly contains H, since a is not in H. Maximality among proper homogeneous ideals gives H+(a)=A. Therefore there exist h in H and x in A with 1=h+ax. Project to degree zero, obtaining 1=h_0+a x_(-n). Passing to D gives d q(x_(-n))=1, and q(x_(-n)) belongs to D_(-n). This proves every clause of the new statement, without claiming H is an ordinary maximal or prime ideal. In particular torsion in M causes no difficulty. The new node itself contains only its statement, not these proof steps.

## Searches

Before introducing the child I searched the whole DAG, including titles and statements, for homogeneous maximal ideals, maximal homogeneous ideals, graded fields and graded division rings; searched the Lean source for these notions; and ran blueprint_refs.py search for homogeneous maximal, graded field and homogeneous quotient. No existing node states the new result. The apparent homogeneous-maximal hit lem-sfb-graded-local-attraction-regularity is a different regular-local-ring criterion, distinguished below. Searches for stabilizer ideal and opposite homogeneous likewise give no blueprint equivalent to the item. Both same_as lists are empty.

I ran leanfinder in two phrasings for each statement, loogle and grep for each, and leansearch for each, all through the prescribed msearch.py with Q112 and this item. All services answered; the actual stdout is in search-*.txt. No unavailable search is misreported as a negative result. The child's grep was restricted to RingTheory, as the recorded sub field confirms. The item retains its inherited historical records and appends the new ones.

I read Mathlib/RingTheory/GradedAlgebra/Homogeneous/Ideal.lean:20–100, including Ideal.IsHomogeneous and HomogeneousIdeal; these are definitions and lattice infrastructure, not a graded-field quotient theorem. The ordinary Ideal.Quotient.maximal_ideal_iff_isField_quotient at Mathlib/RingTheory/Ideal/Quotient/Basic.lean:164 requires an ordinary maximal ideal, which need not be homogeneous; it cannot be used in one line. For example, k[t,t^-1] with its usual Z-grading has homogeneous maximal ideal 0, although it is not a field. I also read HomogeneousLocalization.Away.span_mk_prod_pow_eq_top at Mathlib/RingTheory/GradedAlgebra/HomogeneousLocalization.lean:949; it generates a localization from given algebra generators and has no stabilizer-ideal hypothesis or opposite-product conclusion. The homogeneous prime criterion found by LeanFinder assumes an ordered cancellative grading, not an arbitrary abelian group, and does not assert the new quotient theorem. None is an exact match or a one-line specialization. There are zero Mathlib leaves.

## Not duplicates

lem-sfb-homogeneous-maximal-graded-field-quotient vs lem-sfb-graded-local-attraction-regularity: the existing result assumes a Noetherian Z-graded ring with specified degree-zero local ring and a particular ordinary homogeneous maximal ideal, and proves regularity of a localized quotient; the new result constructs a maximal proper homogeneous ideal above any proper homogeneous ideal for arbitrary abelian-group gradings and proves homogeneous inverses, with no regularity assumptions.

lem-sfb-homogeneous-maximal-graded-field-quotient vs lem-sc-finite-pi-away-fractions: the existing result compares finite vectors of localized fractions and their degrees; it asserts no existence of homogeneous maximal ideals.

lem-sfb-homogeneous-maximal-graded-field-quotient vs def-trf-normal-cone-residue-fibre: the existing node defines a scalar-extended associated graded algebra, whereas the new node proves existence and homogeneous inverses in a quotient.

lem-sfb-homogeneous-maximal-graded-field-quotient vs lem-sfb-homogeneous-primary-decomposition: the existing node gives primary decompositions over a field polynomial ring with its nonnegative total grading; it does not give homogeneous unit quotients for arbitrary group gradings.

lem-sfb-homogeneous-maximal-graded-field-quotient vs def-nagata-homogeneous-localization-degree-zero: the existing node defines degree-zero fractions; it has no homogeneous maximal quotient assertion.

lem-sfb-homogeneous-maximal-graded-field-quotient vs lem-sfb-locally-free-tail-chart-flatness: the existing node gives flatness and a colimit model for a degree-one chart of a sheaf algebra; the new node concerns ideals and homogeneous inverses in arbitrary commutative graded rings.

lem-sfb-homogeneous-maximal-graded-field-quotient vs def-weil-pbc-proj-twisting-sheaf: the existing node defines twisting and associated sheaves on Proj; the new node has no scheme or twisting sheaf.

lem-sfb-homogeneous-maximal-graded-field-quotient vs def-weil-pbc-associated-graded-ring: the existing node constructs the ring of successive powers of an ideal; the new node starts with any abelian-group grading and proves a quotient existence theorem.

lem-sfb-homogeneous-maximal-graded-field-quotient vs lem-sc-p1-away-degreezero-exact: the existing result proves exactness of localized degree-zero fractions for a polynomial-ring module sequence; the new result has neither modules nor localization.

lem-sfb-homogeneous-maximal-graded-field-quotient vs lem-sc-p1-away-degreezero-exact-pair: the existing result gives middle exactness and endpoint implications for equal-degree fractions; the new result proves homogeneous ideal extension and inverse existence.

lem-sfb-homogeneous-maximal-graded-field-quotient vs def-sc-degree-zero-module-fractions: the existing node defines a subset of a module localization; the new node has no fraction construction.

lem-sfb-homogeneous-maximal-graded-field-quotient vs lem-sc-p1-away-degreezero-lift: the existing result lifts fractions along a graded module map; the new result constructs an ideal quotient with homogeneous units.

lem-sfb-homogeneous-maximal-graded-field-quotient vs lem-sfb-graded-stabilizer-strong-products: the new lemma has no group-ring ideal equality and no conclusion about products in the original ring A. The item still constructs the proper ideal KA, forces full quotient support using I=J, and lifts an inverse pair to obtain the contradiction. It is not the item or one of its clauses restated.

## Review by Q112

I checked delivery-errors B–E against the actual node text and the local sources named above. The child introduces M, A, all grading laws, homogeneous ideals, the quotient and its graded components. Its quotient notion cites the existing algebra-hom-quotient definition, which I opened in full. It has no hidden nonzero-ring hypothesis: existence of the proper ideal already excludes the zero ring. No nonnegative, ordered, torsion-free, finitely generated, reduced or Noetherian hypothesis is inserted. The source is by tag and label, and its limitation is explicit. The child is statement-only with empty proof and proof_deps, null proof_origin, status unsplit, and searches with actual results. The item statement is byte-identical to the live statement, and all maintainer fields are preserved.

Step 1 uses only the stated grading and finite-sum ideal operations. I checked K is closed under negative signs and multiplication by A_0, that KA is homogeneous by the written projection formula, and that its zero component is in K. This is the crucial correction/simplification to the retained proof: no tensor, residue field or flatness assumption is used. The zero ring is discharged before requiring a proper ideal.

Step 2 cites exactly the new quotient lemma. Its statement gives an H above the proper homogeneous L from Step 1, the nonzero graded quotient, surjectivity on each homogeneous component, and homogeneous inverses. Those are precisely the properties used; the quote in citations.json includes every one. This is the sole external non-elementary step. No statement from a node's proof is borrowed as a black box.

Step 3 cites the homogeneous inverse sentence of that same lemma. Nonzero homogeneous elements are units, so their inverses have opposite degree and a product of two such units is nonzero. This verifies the subgroup laws for N without assuming D is a domain or an ordinary field. The subgroup calculation itself stays an elementary step.

Step 4 constructs the formal group ring E explicitly rather than citing an unproved group-ring quotient identification. Finite convolution verifies the displayed map, generator by generator. If a homogeneous image is nonzero, its degree is in N by definition; otherwise the image generator is already zero. A finite sum of multiples of these generators is killed by the ring map. The equality I=J is used here and nowhere assumed after an unsupported base change. Distinct formal symbols are distinct by their coefficients over the nonzero ring D, even in characteristic 2 or for torsion degrees. This argument is under 600 characters, does not hide a standard comparison theorem, and needs no new node.

Step 5 cites the inverse assertion and the quotient-kernel sentence of def-weil-pbc-algebra-hom-quotient, both opened and copied literally into citations.json. The graded quotient statement supplies lifts a and b in exactly the required pieces. Their product lies in K, hence H, so its quotient image is zero. It is simultaneously 1 by the inverse property. This gives 1 in K, whose definition is exactly a finite sum of the requested products. Empty sums and m=0 cause no exception.

For small cases I checked: A=0, M=0, m=0, the trivial grading with M nontrivial (the equality I=J fails for A nonzero), k[x] with the usual Z-grading (I does not contain t^-1-1), k[x,x^-1] (opposite powers multiply to 1), and k[C_2] in characteristic 2 (the quotient need not be a domain but nonzero homogeneous elements remain units). For the child, L=0 over a graded Laurent ring shows why ordinary maximal-ideal field quotients are the wrong theorem; A=0 admits no proper L, so its statement is vacuous. The chain and degree-zero projection argument above works equally for finite torsion M. The new node is a genuine Zorn/quotient lemma, not an elementary finite-sum rearrangement, and its whole proof is retained here for the next worker.

All proof citations have explicit verbatim statement quotes. No step exceeds 2000 characters (493, 234, 280, 589, 394). The formal map, support comparison and ideal projection are each routine written calculations; there is no long hidden lemma. The new node has no dependency on the item, so it cannot create a cycle. Existing shared-tag nodes are distinguished individually above. No SGA source is used and no statement dispute was found.

## Validation

The first required deliver.py --no-push exited successfully with OK at 960033122e8. A local read-only comparison also confirmed that the item statement is unchanged and that all four citation quotes are literal substrings of the cited statements. Corrected the report count from five to four; the final dry run is rerun on this final report before pushing.
