# Worker report

## Files written

- dag/nodes/sec-six-functors-basics/lem-sfb-dg-injective-resolution-localization.json: item, split; statement unchanged.
- dag/nodes/sec-six-functors-basics/lem-sfb-dg-good-character-embedding.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-good-coresolution-product-total.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-dg-complete-cofree-orthogonality.json: statement, unsplit; no Mathlib match.
- dag/nodes/sec-six-functors-basics/lem-sfb-right-orthogonal-localization-hom.json: statement, Mathlib leaf, CategoryTheory.ObjectProperty.rightOrthogonal.map_bijective_of_isTriangulated, Mathlib/CategoryTheory/Triangulated/Orthogonal.lean:108.
- citations.json: seven verbatim statement quotations covering every proof-step citation.
- searches.jsonl: actual msearch log; retained intact. write_split.py is a sandbox-only generator of these JSON records.

## Attachments

None. Searches for the exact item id and DGModule/DGAlgebra/differential-graded notions in lean/WeilConjectures found no declaration stating this item. Mathlib's ordinary-complex K-injective comparison is not an attachment and cannot specialize in one line to modules over an arbitrarily graded DG algebra.

## WANTED

None. All mathematical sources needed are present in literature/stacks-project/.

## Problems found and corrected

The original node had no proof or proof dependencies. Its statement is correct and remains byte-for-byte unchanged. The construction must establish acyclicity of the whole Hom complex, whereas 09KS states vanishing only of degree-zero homotopy classes; Step 3 applies the filtration lemma to all shifts and writes the Hom-complex shift identification. Step 4 applies the localization argument to every homotopically injective target, not just the particular filtered resolution constructed in Steps 1–3.

## Source error

Stacks dga.tex Tag 09KU, lemma-right-resolution, has two indexing slips in its proof, not in its statement. Its displayed coresolution repeats I_1 after f_1; it should continue to I_2. Its instruction to add a factor I'_{i+1} to F_{2i}=product_{j>=i} I_j does not define the required intermediate refinement: that factor already lies in this tail. For example take A=Z in degree zero, E_0 the contractible complex Q/Z --id--> Q/Z in degrees 0 and 1, E_0' its degree-1 subcomplex, Y=E_0 with the identity embedding, and E_i=0 for i>0. These are valid good coresolution data. The printed instruction leaves F_1=F_0=E_0 and F_2=0, so the layer F_1/F_2 has nonzero differential and is not a product of shifts of A-dual (all of which have zero differential here). The correct intermediate term has column i constrained to E_i', and all later columns unrestricted. Thus F_{2i}/F_{2i+1}=(E_i/E_i')[-i] and F_{2i+1}/F_{2i+2}=E_i'[-i]. Step 3 states this formula and checks that it is a DG submodule. No item statement or unit statement is disputed or weakened; this repairs the source proof's indexing while retaining its route.

## What remains

No part of the one-level split remains unfinished. The three new non-Mathlib statements are intentionally unsplit for the next workers. There is no Lean writing, compilation or build. Delivery dry-run and push results are recorded below when complete.

## Not duplicates

lem-sfb-dg-complete-cofree-orthogonality vs lem-sfb-dg-injective-resolution-localization: both cite 09KS, but the new node assumes a specified complete graded-split dual-free filtration and concludes only null-homotopy of degree-zero maps from acyclic modules; the item constructs resolutions for arbitrary modules and proves all-degree Hom acyclicity, comparison and naturality. The new node is a strict technical input with a stronger hypothesis, not a restatement of an item clause.
lem-sfb-right-orthogonal-localization-hom vs lem-sfb-left-orthogonal-localization-hom: the existing leaf fixes a source left orthogonal to E and compares Hom(P,N); the new leaf fixes a target right orthogonal to E and compares Hom(N,I), using the distinct Mathlib declaration at line 108 rather than 124. No node states the new leaf already.
lem-sfb-good-coresolution-product-total vs lem-sfb-left-resolution-single-row-total: the existing node identifies a diagonal-coproduct total of a single nonzero row with that row; the new node has infinitely many potentially nonzero columns, product totalization and exact differential-cokernel rows, and concludes a quasi-isomorphism.
lem-sfb-dg-good-character-embedding vs lem-trf-filtered-injective-resolution: the latter concerns bounded-below finite-filtered complexes in an arbitrary abelian category with enough injectives, with injective graded pieces; the new node concerns arbitrary unbounded modules over a noncommutative graded DG algebra, its character dual, and injections on differential cokernels. The trf statement supplies neither the DG-linear embedding nor the two dual-free layers.

Before creating any node I searched all dag/nodes by tags 09KT, 09KS, 09KR, 09K2, 09J0 and labels good-sub, good-right-resolution, property-I and rightOrthogonal.map_bijective, then inspected statements of the plausible orthogonality, totalization and resolution matches. A source-field tag scan finds only the item itself sharing 09KS with the filtered input. Whole-blueprint searches (blueprint_refs.py search) for 09KT, 09KS, 09J0, good-right-resolution, property (I), product total, cofree, dual free, right orthogonal and rightOrthogonal.map_bijective found no match. Each new id was also searched in the whole DAG and project Lean before creation. same_as is therefore [] on each node.

## Review by Q21

I read dga.tex section-I-resolutions in full, especially the property (I) definition and Tags 09KR, 09KS, 09KT and 09KU, together with Tag 09KY(2) and its dual proof. I also read the graded character-dual construction preceding Tag 09K2 and the Hom-into-dual formula 09K4, and homology.tex Tag 09J0 including its product-total differential. I read the latest blueprint's sk-thm-sf-ctf-stability-direct-images.proof.md (3) and the inherited unit/chapter records. This is the inherited DG adjunction prerequisite below that route, not a replacement of its geometric argument. blueprint_refs.py ancestor returned None, so the inherited null ancestor and entire via chain are retained and extended on the new nodes.

The new good-embedding statement agrees with 09KT: no boundedness or commutativity is assumed; both the degreewise injection and the induced injection on M^n/d(M^{n-1}) are stated. The two layers are DG products of shifts of A-dual. Their graded splitting follows from the graded injectivity of these products in the preceding section and 09K2. I checked the explicit right action lambda*a(b)=lambda(ab) and dual differential (-1)^{n+1}lambda*d_A against the source; it is the dual of the left regular module. The empty product and M=0 are allowed. For A=Z in degree zero this is an ordinary character-dual embedding, including nonzero differentials; it does not assert that every arbitrary degreewise embedding preserves differential cokernels.

The totalization input states exactly 09J0 for abelian groups: the horizontal complex begins in degree zero but the individual complexes are unbounded, the augmented rows and all cokernel rows are exact, and the conclusion concerns the augmentation into the product total. The formula includes f_{i-1}x_{i-1} in coordinate i; this checks total degree and the i=0 boundary. For only column zero nonzero, the assumptions force the augmentation to be an isomorphism; for all-zero data the total is zero. No direct-sum total or unjustified spectral-sequence convergence is used.

The filtered-orthogonality input is precisely 09KS with property (I) expanded: completeness, graded sections of quotient transitions, and dual-free product layers. It concludes only a homotopy in degree zero. It imposes no DG splitting and no boundedness. This is why it is strictly smaller than the item's existence-plus-comparison statement. The zero filtration on zero and a one-layer product of shifted duals satisfy it; a finite two-layer extension needs only a graded section, as the source requires. The unresolved proof of its complete-filtration theorem belongs to its own future split, not an unrecorded lemma inside this item's steps.

The generic right-orthogonal input was checked directly against Mathlib/CategoryTheory/Triangulated/Orthogonal.lean:108–121 and ObjectProperty/Orthogonal.lean:34–39. Taking the object property to be membership in E gives exactly W_E and vanishing of every Hom(E,I). Its source and target Hom universes are arbitrary, and it does not require a triangulated target category. This is an exact Mathlib leaf. With E=0 the assertion is localization at isomorphisms; with I=0 both Hom sets have their single zero map.

Step 1 cites only the good-embedding statement: it supplies the map and layers that the induction uses. I checked M_{i+1} is the actual DG cokernel and f_i is quotient followed by the next injection, so the horizontal square is zero and each row is exact. No property of a hidden construction of that node is taken.

Step 2 cites the good-embedding statement for injectivity of the cokernel maps, and the totalization statement for the quasi-isomorphism. Right exactness of differential cokernels is written out by lifting a boundary in the preceding degree; splicing then verifies exactly the extra hypotheses of 09J0. I checked that the total differential squares to zero, and that its internal Leibniz sign is (-1)^i(-1)^{n-i}=(-1)^n. Thus the product total is a right DG module, not just an underlying abelian complex, and the augmentation is DG-linear. These algebraic identities are the elementary assembly within the cited non-elementary step.

Step 3 cites the good-embedding statement for its graded splitting and product layers, and the filtered-orthogonality statement for null-homotopy after the explicitly defined complete filtration. I checked each quotient, the horizontal differential direction, compatible-coordinate completeness, and that coordinate and graded sections give the exact transition splitting required. This corrects the source indexing slips described above. Applying the same lemma to shifted filtrations is legitimate because their layers are shifted products of the same duals; the Hom-complex differential is also shifted by (-1)^r. This proves all cohomology vanishing rather than assuming 09KS already says it.

Step 4 cites the existing lem-sfb-dg-homotopy-acyclic-localization statement, which I opened and read: it says K(A,d) is triangulated, the acyclic full subcategory is triangulated, and its cone class is exactly the quasi-isomorphisms. It has the same arbitrary associative DG algebra and right-module conventions. Its choice of cone-triangle third-map sign does not change that cone class. The new generic right-orthogonal leaf then applies with J right orthogonal by H^0 Hom acyclicity. This uses the cited statements, not their proofs, and proves the specific localization map is bijective for every such J.

Step 5 is elementary: Q(bfa)=Q(b)Q(f)Q(a) is functoriality, inverse naturality follows from uniqueness in a bijection, and Hom(C,J[r])=Hom(C,J)[r] follows by substituting the two differentials. I checked negative and positive shifts and zero modules; no choice of arbitrary comparison isomorphism changes the specified map. The universe convention covers the set-indexed character products and countable total; there is no covert finite-generation, flatness or boundedness assumption.

For B1–B10 all four new records are self-contained statements with named objects and hypotheses, single-escaped TeX, exact source places, empty proof/proof_deps, filled blueprint.from.place and same_as. The sole leaf records its declaration, file and verified line. Every search in a new node is copied from the real searches.jsonl with the identical tool and query. I read the returned hits and tried a second semantic phrasing for each nonmatch: ordinary CochainComplex K-injectivity, CM5b factorization, and ungraded CharacterModule facts do not specialize to these DG statements; generic orthogonal localization does match and is recorded as a leaf. For C1–C8 the seven citations have verbatim statement quotes, no definition substitutes for a theorem, and no cited node depends back on the item. All cited statements have the item's unit or are Mathlib leaves, so no off-unit tool permission is needed. D1–D5 are met by constructing the coresolution and filtration in the item's steps, rather than making a new existence or comparison clause. E1–E7 are checked in the hypothesis and edge-case discussion above. Each non-elementary step has fewer than 2000 characters; none conceals an additional independent identification or convergence lemma. No SGA source is used.

## Validation

Initial required deliver.py --no-push completed successfully: preflight passed at ef5c5de03f4. It ran the server checks and created the durable dry-run receipt. A final dry run follows the report corrections and TeX normalization.
