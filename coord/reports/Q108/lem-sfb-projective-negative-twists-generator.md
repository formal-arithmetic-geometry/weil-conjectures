# Stage-1 report: lem-sfb-projective-negative-twists-generator

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-projective-negative-twists-generator.json: item split, statement unchanged, five proof steps following Stacks 0A9V.
- dag/nodes/sec-six-functors-basics/lem-sfb-projective-coordinate-koszul-sequence.json: statement, unsplit; no Mathlib match after LeanFinder, Loogle, grep and LeanSearch.
- dag/nodes/sec-six-functors-basics/lem-sfb-ample-twist-hypercohomology-detection.json: statement, unsplit; no Mathlib match after LeanFinder, Loogle, grep and LeanSearch.
- citations.json: verbatim statement quotations for every node cited in every item step.

## Attachments

None. I searched lean/WeilConjectures for the item's blueprint tag and the concepts negative twists, projective-space generators, weak generators, and Beilinson. WeakTriangulatedGenerator.lean defines the notion but does not prove this item. FiniteLocallyFreeDerivedHom.lean proves a useful separate statement, not the generator assertion. No declaration found meets the exact attachment criterion.

## WANTED

None. All source inputs used are available in literature/stacks-project.

## Findings and changes

The item was an empty unsplit statement sourced to 0A9V. Its arbitrary-ring, arbitrary-dimension and unbounded-complex quantifiers agree with the source and were retained. The proof is now the actual 0A9V argument, with the negative-twist induction made explicit. I used the ambient sheaf-module derived category for the orthogonal and the bounded replacement complex, avoiding a separate unstated triangulatedness assertion about the quasi-coherent full subcategory. The new nodes are the two independent geometric inputs, 0BQS and 0BQR, rather than a restatement of the finite-generator conclusion.

A tempting existing citation, lem-weil-pbc-ringed-site-locally-free-derived-hom, is bounded below in its target and would not apply to K here. I did not cite it. The actual proof uses unbounded perfect duality, global RHom, and the shifted-hypercohomology comparison. The existing lem-sc-finite-locally-free-derived-hom is used only with target O_X in degree zero to identify the dual line bundle, exactly within its scope.

The current blueprint was read under literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-thm-sf-ctf-stability/, including the unit and direct-images proof. This is the established projective-space tilting prerequisite deep below direct image stability, not a replacement for a unit step. tools/blueprint_refs.py ancestor returns None for the item's inherited ancestry; new nodes retain that exact value and prepend this item to the inherited via list. The inherited place describes the direct-images prerequisite through 0CSG and 0BQU, with 0A9V as the generator input.

## Searches and reuse

I searched the whole DAG for tags 0A9V, 0BQS, 0BQR, their labels, and the concepts Koszul sequence, ample nonzero cohomology, negative-twist generation, and global derived Hom. I ran tools/blueprint_refs.py searches for generator, Koszul, construct-the-next-one, nonzero-some-cohomology, 0BQS, 0BQR, line bundle, derived Hom, hypercohomology and Koszul sequence. None states either new node. The broader searches found the existing perfect-duality, orthogonal and bounded-devissage tools, which I reused.

Every new node has four actual msearch.py calls recorded in searches.jsonl. The LeanSearch phrasing differs from the LeanFinder phrasing. The coordinate-sequence hits are ordinary projective resolutions or cotangent sequences; their displayed types do not concern sheaves O(a) on projective space. The ample-detection hits concern t-structures and quasi-coherent presentations, without ample twists or hypercohomology detection. Loogle and source grep give no relevant match. The item was also searched through all four services; abstract derived-category constructions and morphisms from projective objects do not prove projective-space generation. Additional logged searches for a possible line-bundle derived-Hom node were exploratory: the existing stronger tools made that new node unnecessary. No unrun query or unavailable service was represented as a successful negative search.

## Not duplicates

There is no existing node with source tag 0BQS or 0BQR. The following conceptually nearby nodes were checked directly:

lem-sfb-projective-coordinate-koszul-sequence vs lem-sfb-projective-negative-twists-generator: the new statement is an exact finite sequence of line bundles for each integer a; the item detects all derived objects by finitely many Hom groups, and the induction remains in the item's proof.

lem-sfb-ample-twist-hypercohomology-detection vs lem-sfb-projective-negative-twists-generator: detection allows every nonnegative ample power on any scheme with an ample line bundle; the item gives a finite set of negative twists on projective space. Reducing the infinite powers to the finite set is the independent Koszul argument in step 2.

lem-sfb-ample-twist-hypercohomology-detection vs lem-pc-very-ample-ample: the existing node asserts ampleness over a field; it does not assert detection of an unbounded derived object. Likewise lem-trf-proj-qc-open-twist-ample supplies ample twists but contains no derived-cohomology detection assertion.

## Tool uses

The split_report declares four generic off-unit tools: bounded-complex triangulated devissage, finite-locally-free derived Hom into a degree-zero sheaf, global RHom sections, and shifted global RHom hypercohomology. Their exact statements supply the finite complex construction and the Hom/cohomology comparisons; no same-unit node supplies these statements in these generalities. The left-orthogonal closure node is already a Mathlib leaf. The perfect-duality input is in the item's unit. These generic tools leave the geometric proof route unchanged.

## Review by Q108

I read perfect.tex at lemma-generator-P1 (0A9V), lemma-construct-the-next-one (0BQS), and lemma-nonzero-some-cohomology (0BQR), with the tag-to-label entries in tags/tags open. The item is exactly the generator lemma with E renamed T; the two new statements match the exact sequence and the nonzero hypercohomology lemma. Neither adds a field, Noetherian, boundedness or finite-coherence hypothesis. The sequence maps are specified by the signed graded coordinate Koszul construction; the detection statement explicitly defines its hypercohomology and derived tensor by existing definition nodes. Both new nodes contain only statements and searches, with empty proofs and proof dependencies.

For step 1 I opened lem-sf-shift-stable-left-orthogonal: its statement is the LEFT orthogonal closure for any shift-stable class, exactly the class {K[q]} used here. I checked the summand argument explicitly: f=(f pi_i)iota_i; finite sums need only determination by the summand restrictions. No compactness or infinite coproduct theorem is used.

For step 2 I read the new coordinate-sequence statement and lem-weil-pbc-bounded-complex-triangulated-devissage. The latter applies to the ambient abelian category of module sheaves and any strictly full triangulated subcategory, not only to modules over a ring. With a=-m and m>=n+1, every remaining degree j uses the smaller nonnegative index m-j. The augmentation into the complex in degrees 0 through n is a quasi-isomorphism by the EXACT sequence statement, and devissage puts that bounded complex in the orthogonal. This is an explicit strong induction with bases 0 through n, rather than an appeal to an unnamed thick-generation theorem. I also read derived.tex, lemma-K-bounded-derived, whose proof gives the stupid-truncation triangles behind the existing tool.

For step 3 I opened all five cited node statements. The projective twist definition supplies local rank-one bases and the transition rule. The finite-locally-free derived-Hom theorem applies to target O_X[0] and identifies the dual with ordinary sheaf Hom. Dualizing the transition functions gives O(m); multiplying rank-one bases identifies O(m) with O(1) to the mth tensor power. The ringed-site perfect-duality theorem permits EVERY unbounded target. lem-pur-rhom-global-sections identifies H^0 internal RHom with actual morphisms, and lem-sc-global-hom-shifted-hypercohomology with indices (0,q) supplies degree q, again without boundedness. I read sites-cohomology.tex, 08JA and 08JJ, and cohomology.tex, 08DQ, to check this use against the sources. I wrote the tensor swap explicitly (the line is in degree zero), so no sign or unnamed comparison is hidden.

For step 4 I opened the precise absolute ampleness definition def-weil-pbc-ample-invertible-module and checked properties.tex, definition-ample (01PS). This definition works over every commutative ring, unlike the existing proper-over-a-field criterion. The standard affine cover is finite, hence X is quasi-compact; the coordinate sections are written on every U_j and their nonvanishing opens are exactly the U_i. These two clauses verify the definition directly, so this remains an elementary step rather than a new ampleness theorem.

For step 5 the new 0BQR statement applies because K has quasi-coherent cohomology, no boundedness is needed, and step 4 provides the ample line. It contradicts the vanishing for EVERY m and q proved earlier. The definition def-pc-generators has exactly this weak-generator interpretation. Every cited node has a verbatim quotation in citations.json; I used statements, not unpublished constructions inside their proofs.

I tested n=0: the coordinate sequence is 0->O(a)->O(a+1)->0 with the invertible coordinate x_0, and the generator reduces to O on Spec(A). For n=1 it is 0->O(a)->O(a+1)^2->O(a+2)->0; the induction for m=2 uses only O(-1) and O. For n=2 the multiplicities are 1,3,3,1, confirming the n+1 indexing. The source proof has an intermediate displayed binomial using n, but the source lemma and its final sheaf sequence both use n+1; the new statement follows those correct formulas. Zero rings give the empty projective scheme and a vacuous detection assertion. Nilpotents in A do not affect the coordinate Koszul exactness (on each standard open a coordinate is a unit); no regularity of A is used. Shifts of arbitrary quasi-coherent modules and unbounded complexes remain allowed, since no Serre vanishing or bounded-below Hom theorem was inserted.

Against delivery-errors B-E I checked self-contained objects and definition dependencies, undoubled TeX, exact tags and labels, actual logged searches, absence of a duplicate or attachment, statement-only new nodes, exact hypotheses in each cited statement, no uncited non-elementary input, explicit induction, and no replacement of the goal by one of its clauses. All steps are below 2000 characters. The comparison and finite-complex facts are already existing nodes. No statement dispute or source correction to the item is needed. No other agent read this split, as required for this direct delivery.

## Unfinished work

None in this one-level split. The two new nodes deliberately remain unsplit stage-1 items.
