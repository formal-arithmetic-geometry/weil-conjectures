## Worker report

Item: lem-pur-coordinate-graph-localized-jacobian. Group: Q42. Stage 1 only, direct delivery.

### Files written

- dag/nodes/sec-smooth-purity/lem-pur-coordinate-graph-localized-jacobian.json: statement retained verbatim, seven-step proof, exact proof-dependency union, blueprint place retained and same_as checked, split_report and actual additional Mathlib searches.
- citations.json: twenty entries, one for every step/dependency pair, quoting the cited statement verbatim.
- report.md: this report and signed reading.

No new DAG nodes, no new Mathlib leaves. The argument needs only existing Mathlib leaves and definition nodes. searches.jsonl is the command-generated log; write_split.py is a sandbox-only preparation script, not a project or launcher modification.

### Attachments

None. Searched lean/WeilConjectures by the full item id, graph/Jacobian and cotangent-basis terminology. No project declaration gives every clause of this item under its hypotheses. The upstream matrix Schur-complement files are general tools, not attachments for the specified graph and its algebra structure. No compiler was run.

### Literature and blueprint

Read GOAL.md, the three route levels of SETUP.md, the worker and stage-1 brief, stages/1-dag.md, the chapter/unit records, and delivery-errors B through E. Read the current latest chapter and sk-prop-an unit, plus lem-pur-regular-immersion-linearization.md and its proof. The applicable sentence is the second paragraph's passage from the chosen differential basis to the prescribed etale coordinate map. Its block algebra is below the unit level and changes no purity route. No SGA source is used.

Read Stacks algebra.tex, definition-standard-smooth (00T6), lemma-standard-smooth (00T7), especially part (2) and its proof solving the differential relations, and example-make-standard-smooth. Also read morphisms.tex, lemma-etale-at-point (02GU), especially condition (8). The item includes extra explicit matrix and quotient identities rather than a verbatim statement of either tag; its proof_origin is therefore agent, with its blueprint place and Stacks support specified. There is no need to invoke the etale-at-point equivalence in this item's proof: it establishes the concrete square presentation that its parent needs.

WANTED: none.

### Existing material and searches

Searched the whole DAG by the two source tags, Schur complement, graph presentation, cotangent/differential basis, determinant identities, and localization/quotient terminology; opened the statements of all twenty step citations. Ran blueprint_refs.py ancestor for the item and searched Jacobian, Schur, Schur complement, standard smooth, localization and determinant. No blueprint node duplicates the full item. Existing standard-smooth basis, polynomial differential formula, adjugate, block determinant, determinant multiplication and localization universal-property nodes suffice; the graph/localization comparison is proved here rather than moved into a duplicate node. In particular the affine-chart node has additional geometric hypotheses and is not used as a substitute for this algebra calculation.

The required msearch.py commands were run for the item with LeanFinder twice, Loogle, LeanSearch and grep twice; their exact query strings and returned names are added to mathlib_searches from searches.jsonl. Read the returned hypotheses in RingTheory/Smooth/StandardSmoothOfFree.lean and Extension/Cotangent/Free.lean: they require a global differential basis or an existing submersive presentation, not this basis after tensoring with a residue field. Read the localizationAway Jacobian declarations in Extension/Presentation/Submersive.lean and det_fromBlocks₁₁ in LinearAlgebra/Matrix/SchurComplement.lean. These prove separate constituents, not the whole item. No search failure was recorded as absence. The earlier Q121 searches in the repository node were preserved, not represented as freshly run by Q42.

### Problems and unfinished work

No statement dispute or correction. The source statement is consistent, including its row convention, the derivative of H_j-T_j over R, and the empty matrices. Its previously empty proof is now supplied. No missing result remains for this one-level split. The general localization presentation already in the DAG was not introduced as a new node or cited merely for an internal construction; step 6 directly proves the two inverse maps from the cited universal properties.

## Not duplicates

No new nodes. All reusable facts are citations to the existing DAG, and no same-tag new/existing pair is introduced.

## Review by Q42

I checked the statement against 00T6 and 00T7 with the actual presentation in view: the prescribed first r minor is a unit in A, not just nonzero at one point, so 00T7(2) gives the basis of the last d differentials over A. The determinant in Stacks is transposed relative to our row convention; the finite permutation formula gives the same determinant. The second paragraph of the current linearization blueprint calls for the particular functions chosen there, so replacing them by some other etale coordinates would not suffice. This split keeps H_j and the specified action T_j -> h_j throughout.

Step 1 cites the statement of lem-weil-pbc-standard-smooth-kahler-basis for exactly that free basis, and def-weil-module-base-change for the tensor. I did not infer freeness of a fibre from a rank claim: both inverse fibre-coordinate maps are displayed, so no flatness hypothesis on K is used.

Step 2 cites lem-weil-pbc-polynomial-ring-kahler-basis, whose statement includes dg=sum partial(g) dx, and the universal derivation definition. Its induced map sends dy_b to da_b; therefore the F rows vanish and the H rows give dh_j. Tensor functoriality is expressly in def-weil-module-base-change. No conormal injectivity assertion is taken from a definition node.

Step 3 uses the standard-smooth definition only for its actual unit minor, the determinant definition only to commute the finite formula with ring maps, and the adjugate-identity node for its stated two-sided product. Multiplying by the scalar inverse constructs B-bar inverse; solving the displayed relations then gives the precise Schur coefficient matrix, with the minus sign and row/column convention checked. Step 4 constructs the inverse coefficient matrix Q from the assumed second basis; comparison in both bases proves QS=SQ=I. The Cramer/determinant-identity node is used only for its expressly stated multiplicativity, never for an unstated basis criterion. Its n>=1 hypothesis is checked by using it only when d>0.

Step 5 again uses that multiplicativity only for n>0 and the existing block-triangular determinant node, whose statement permits zero block sizes. Its statement is for a lower triangular block, so I explicitly apply it to the transpose for the upper triangular product, with the permutation-inversion argument for transpose invariance written in the step. This avoids quietly asking the node for a different matrix theorem. The localization-at-prime definition kills every element of q in K, which is all that is needed to deduce delta is not in q. There is no assumption that the residue field equals k or that q is maximal.

Step 6 is an elementary universal-property argument. The polynomial node actually states evaluation and uniqueness on generators; the algebra/quotient node states surjectivity and kernel; the localization node actually states factorization and uniqueness. I checked every relation is killed and both composites, including the new variable t. The graph relation [H_j]=[T_j] is what makes the inverse R-linear. Uniqueness of inverses proves that t is fixed; no unproved identification of abstract algebras substitutes for this verification.

Step 7 uses formal partial derivatives over R, so T_j is constant in the y derivatives. The augmented matrix has a zero top-right block and bottom-right entry Delta, exactly the lower-block hypothesis of the cited determinant node. Thus the determinant is Delta squared with no sign or congruence qualification. The square-Jacobian definition is used only after the isomorphism and unit have been proved, for its literal definition of a specified square presentation.

I checked r=0 (ordinary polynomial algebra), d=0 (no H rows and zero-dimensional differential module), and r=d=0 (A=k, Delta=1 and the presentation k[t]/(t-1)). In characteristic p the example r=0,d=1,H=y^p does not satisfy the differential-basis hypothesis, whereas H=y+y^p has differential 1 and gives a unit determinant as required. For a nonclosed prime, the argument still works over its actual residue field. All seven steps are under 2000 characters; none conceals a new comparison theorem. I corrected a potential citation overreach while drafting by proving the fibre-basis maps and the transpose determinant identity explicitly instead of treating them as contents of the standard-smooth or lower-block determinant node. Every quoted statement in citations.json was copied from the node used, and proof_deps is exactly the union of uses.

### Dry-run repair

The first preflight identified a TeX row separator immediately followed by the letter t in the augmented matrix as a doubled command. Inserted a space after that matrix row separator and reran the required checks; no mathematical text changed.
