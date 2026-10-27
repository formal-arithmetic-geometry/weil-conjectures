# Stage-1 report: lem-sfb-strong-grading-torsor-algebra

## Files written

- `dag/nodes/sec-six-functors-basics/lem-sfb-strong-grading-torsor-algebra.json`: existing statement node split into eleven fully written steps; no Mathlib match for the whole item. Its statement, statement dependencies, inherited source qualifications and blueprint provenance are preserved.
- `citations.json`: verbatim statement quotations for all fourteen uses in the proof, covering thirteen distinct existing nodes.
- `report.md`: this report. `searches.jsonl` contains the actual searches made by msearch; `write_split.py` is sandbox-only preparation material.

No new DAG nodes, no new Mathlib leaves, no Lean files and no compiler or Lake invocation.

## Attachments

None. Searched the live read clone's `lean/WeilConjectures/` for the exact item id, strong grading, graded torsors and Hopf–Galois terminology. There is no project declaration giving the item. Ordinary grading constructions in Mathlib do not prove it.

## WANTED

None. This auxiliary was expressly formulated as an independent algebra argument, rather than as the statement of Conrad or of Tag 0EKK. The local Stacks documents and existing DAG lemmas suffice. I have marked the proof origin as agent-written.

## Findings and proof route

No STATEMENT-DISPUTED finding: the statement is correct as written, including arbitrary coefficient changes and zero rings. There was no earlier item split in this sandbox, only dispatcher brief markers. I copied the current unsplit item and retained its inherited searches and provenance. I read the source argument preserved in `coord/reports/Q131/lem-sfb-relative-affine-multiplicative-quotient.md`.

The source's scope matters: Stacks `groupoids.tex`, example-Gm-on-affine and Tag 0EKK, lemma-complete-reducibility-Gm, establish the action/grading dictionary for the multiplicative group, not faithful flatness, finite presentation or the torsor theorem. The split does not claim otherwise. I read those passages and the relevant passages of `algebra.tex`, `morphisms.tex` and `schemes.tex` cited below.

I replaced the parent report's suggested local-line-bundle proof of flatness by an explicit retraction from a free module. This proves the same argument's projectivity assertion directly and avoids needing separate nodes for finite principal covers, local freeness and arbitrary direct sums of flat modules. For finite presentation I use the existing general group-algebra presentation with zero subgroup, followed by the existing faithfully flat descent theorem, after proving the tensor comparison. This uses no new geometric quotient theorem or change to the chapter/unit route. Finite generation of M is used precisely at the group-algebra presentation, not during the flatness or comparison calculations.

Read the chapter and unit records and the current blueprint through `literature/blueprint/latest/`, including its direct-images proof, paragraph (3). The inherited chain is a structural prerequisite of that paragraph via the relative affine multiplicative quotient. The ancestor command returns None; I retained the inherited null ancestor, detailed place and full via chain. Whole-blueprint searches for `graded` and `strongly graded`, and DAG searches by statements and titles, found no node stating the whole item. No chapter or unit record is changed. All proof citations outside the unit are existing Mathlib leaves or definition nodes; the subgroup-algebra presentation is in this item's unit.

## Mathlib searches

Ran the required wrapper for this item with LeanFinder, Loogle, grep and LeanSearch, followed by a second LeanFinder phrasing. The queries and actual result digests are recorded in `searches.jsonl` and appended to the item's inherited `mathlib_searches`; no unavailable result was called an absence. All services returned answers. The strong-grading/Hopf–Galois/diagonalizable-torsor grep had zero hits. Loogle's combined GradedAlgebra and Module.FaithfullyFlat query had zero hits. Semantic hits give ordinary grading constructors, homogeneous generators under an already-assumed finite-type hypothesis, free-module faithful flatness and tensor/Hopf constructions. None is the theorem of this item.

Read `GradedAlgebra/Basic.lean`, `FiniteType.lean` and `TensorProduct.lean`, and `Flat/FaithfullyFlat/Basic.lean` in the pinned Mathlib. The finite-type theorem assumes its finiteness premise; the general base-change grading instance supplies part of the final clause but does not state the full item, nor are its subparts new nodes here. An exploratory wrapper grep and source read of `AlgebraicGeometry/Morphisms/Flat.lean` confirmed the single-affine flatness equivalence, then the existing DAG node for it was reused. No source grep was passed off as an unrun search.

## Not duplicates

No new nodes were created. Existing nodes were reused for projective flatness, the maximal-ideal faithful-flat criterion, the subgroup group-algebra presentation, faithful-flat finite-presentation descent, and the affine-scheme dictionary. In particular the group-algebra presentation is specialized to L=0 and coefficient ring A, rather than restated as a new finite-presentation lemma. The action/grading nodes and the field/Noetherian torus quotient theorems found by the original search do not prove this arbitrary-ring strong-grading assertion.

## Review by Q48

I checked the statement clause by clause and every use against the cited node's actual statement. I read delivery-errors B–E in full. There are no new self-contained statements or duplicate pairs to audit, no clause moved to a replacement node, and no hidden appeal to a fact under a Stacks tag without a corresponding citation or an explicit elementary calculation.

Step 1 uses only the hypotheses: multiplication by B preserves each degree, which makes the degree projections B-linear. The index set is a set with a finite fibre J_m over each m, and the coefficient vector i(a) is finitely supported. I checked that v_(m,j) a_m lies in B, that p i is the identity, and that the displayed decomposition of F has both inverse identities. Thus A is a direct summand of an actually specified free module; no local-freeness lemma is hidden.

Step 2 cites `lem-weil-pbc-projective-module-flat`, whose statement applies to a direct summand of a free module over any commutative ring. Its local-Artinian Stacks source is used only for the explicitly general projective-implies-flat sentence, not for its local-Artinian equivalence. The second cited node, `lem-weil-pbc-flat-faithfully-flat-maximal-ideals`, requires flatness and proper extended maximal ideals. The degree-zero projection proves the latter directly; no assertion that a split ring inclusion is automatically flat is made. I read Tag 00HP, lemma-ff, and confirmed precisely these hypotheses.

Step 3 cites `def-sfb-ring-diagonalizable-group` for the basis multiplication, coproduct and counit, and `lem-weil-pbc-algebra-tensor-pushout-universal-property` for the actual induced algebra map. The maps agree on B because B has degree zero. Multiplicativity, the counit and coassociativity are evaluated on homogeneous elements, then extended by finite sums. This is the general-group calculation itself, not an unjustified invocation of the G_m-only source.

Step 4 takes from the same group-algebra definition only the finite basis expansion. Coefficient maps give the inverse description after tensoring with A, so no flatness is assumed in describing that tensor product. The formula defining gamma is A-linear on those basis coefficients. Step 5 verifies both composites: in the second identity b_m v_(m,j) lies in B and can therefore be moved across the balanced tensor product. I checked the order of the two factors and the negative degree of v. Bijectivity of a ring homomorphism gives an algebra isomorphism, without having to prove multiplicativity of the proposed linear inverse separately. These steps are explicit finite-sum and balancing identities, not standalone facts deferred to another node.

Step 6 cites the actual conclusion of `lem-sfb-subgroup-algebra-coset-presentation`: finite presentation of the coefficient group algebra when the quotient group is finitely generated. Here the coefficient ring is A and L=0, so the hypothesis is exactly the given finite generation of M; A[0] is A by its single basis element. The explicit coefficient isomorphism identifies this algebra with A tensor_R R[M]. The other cited node, `lem-weil-pbc-finite-presentation-descends-faithfully-flat`, has faithfully flat base B to A, original algebra A over B, and extension A tensor_B A over its first A factor. All three match, and faithful flatness was proved before descent is used. I read Tag 00QQ, lemma-finite-presentation-descends. Thus this is target-base descent, not an invalid deduction from finite type or a Noetherian assumption.

Step 7 cites three exact existing statements: morphisms between affine schemes are affine; a ring map is flat if and only if its spectrum map is flat; a faithfully flat ring map is surjective on spectra. I read the corresponding Stacks passages 01SH, 01U5 and 00HQ. In particular I use the single-affine equivalence, not the all-affine-opens node as though one chart verified its universally quantified condition. Step 8 uses the definition of local finite presentation on the single affine chart and the actual permanence lemma's clause (3), which says affine morphisms are quasi-compact and separated, hence quasi-separated. This proves full finite presentation with the project's convention, not just local finite presentation.

Step 9 cites `lem-weil-pbc-fibre-product-affine-spectra`, whose statement includes both tensor inclusion maps for the projections, and `def-weil-affine-spectrum`, which gives contravariant functoriality. I read Schemes 01I4. The first component is the identity and the second is the coaction, so Spec(beta) is the specified right-action comparison with precisely the stated orientation; it is not merely an unspecified isomorphism between the two schemes.

Step 10 proves the arbitrary-base-change grading by tensoring explicit split inclusions and applying their split projections to finite relations. This verifies injectivity, spanning, uniqueness, degree-zero algebra, product degrees and persistence of unit expressions without assuming R' flat. Step 11 gives both inverse maps for the base-changed balanced tensor products and computes beta on their homogeneous generators. Thus the base-changed comparison is the actual beta', rather than merely some isomorphism of its source and target. Applying the preceding argument to the verified new data gives all flatness, finite-presentation and geometric conclusions over R'.

Small cases checked: M=0 gives A=B and the identity comparison; A=0 forces B=0, all tensors and comparisons are zero and both spectra empty; a zero base ring forces this case too. The group algebra example A=R[M], B=R gives the usual torsor comparison. Finite torsion M over a characteristic dividing its order still satisfies the calculation: no derivative, smoothness, reducedness or invertibility of that order is used. For a nonflat base change such as Z to Z/n, the split projections prove injectivity of the component inclusions even though tensoring arbitrary inclusions need not preserve it. The formulas have no denominators and do not impose a finite-presentation assumption on R to A.

No proof step exceeds 2000 characters. Each elementary step is an explicit construction with finite sums and displayed inverse or balancing calculations; the non-elementary flatness, descent and affine-geometric facts have named citations. The new proof does not depend on the parent affine-quotient node, so it introduces no upward cycle. All fourteen citations have complete verbatim statement quotations in citations.json.

## Unfinished work and validation

No mathematical clause remains unfinished. Remote review_split and the required delivery dry run are recorded below as they finish. This report is the author's self-review; independent review is the maintainer's.

Remote `review_split`: PASS, zero new nodes. The unit realization warning is inherited and this auxiliary does not own the unit key statement.
